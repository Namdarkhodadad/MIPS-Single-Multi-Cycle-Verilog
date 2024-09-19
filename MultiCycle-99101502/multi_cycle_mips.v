
`timescale 1ns/100ps

   `define ADD  3'b000
   `define SUB  3'b001
   `define SLT  3'b010
   `define SLTU 3'b011
   `define AND  3'b100
   `define XOR  3'b101
   `define OR   3'b110
   `define NOR  3'b111

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;

   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [2:0] aluOp;
   reg [1:0] aluSelB;
   reg SgnExt, aluSelA, MemtoReg, RegDst, IorD, flagLui, flagJump, flagra, flagPC, flagrfRD1, start, flagr30, flaghi, flagr29, flaglo, flagA, flaghi2, flaglo2;
   reg [31:0] tmp_hi,tmp_lo;

   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;
   wire ready;
   //reg [63:0] multResult;
   wire [63:0] multResult;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt && !flagJump && !flagrfRD1)
         PC <= #0.1 aluResult;
      else if( PCwrt && flagJump && !flagrfRD1)
         PC <= #0.1  {PC[31:28],IR[25:0],2'b00};
      else if(PCwrt && !flagJump && flagrfRD1)
         PC <= #0.1  rfRD1;

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      //.WR( RegDst ? IR[15:11] : IR[20:16] ), 
      //.WR( RegDst ? IR[15:11] : (flagra ? 31 : (flagr30 ? IR[25:21] : (flagr29 ? IR[20:16] : IR[20:16]) ) ) ),
      .WR( RegDst ? IR[15:11] : (flagra ? 31 : IR[20:16] ) ),
      .WD( MemtoReg ? MDR : (flagLui ? {IR[15:0],16'h0} : (flagPC ? PC : (flaghi ? tmp_hi : (flaglo ? tmp_lo : (flagA ? A : aluResult ))))))
      //.WD( MemtoReg ? MDR : aluResult ) 
   );
   wire [31:0] wrtData = MemtoReg ? MDR : (flagLui ? {IR[15:0],16'h0} : (flagPC ? PC : (flaghi ? multResult[63:32] : (flaglo ? multResult[31:0] : (flagA ? A : aluResult )))));

   multiplier1 mult(
      .clk( clk ),
      .start( start ),
      .A(A),
      .B(B),
      .Product(multResult),
      .ready(ready)
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA ? A : PC;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*) 
   case (aluSelB)
      2'b00: aluB = B;
      2'b01: aluB = 32'h4;
      2'b10: aluB = SZout;
      2'b11: aluB = SZout << 2;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),
      .X( aluResult ),
      .Z( aluZero )
   );


   // Controller Starts Here

   // Controller State Registers
   reg [5:0] state, nxt_state; 

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26, EX_JUMP = 27, EX_JAL = 28, EX_JR_OR_JALR = 29, EX_MULTU = 30, EX_MULTU_BEGIN = 31, EX_MULTHI_WRT = 32, EX_MULTLO_WRT=33,
      EX_MFHI = 34, EX_MFLO = 35, EX_MFHI_MFLO_WRT = 36, EX_MFHI_OR_MFLO = 37,
      //
      EX_MFHI_DELAY = 38,
      EX_MFLO_DELAY = 39;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1; 
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;
     // tmp_hi = 'bx; tmp_lo = 'bx;

      PCwrt = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;
      flagLui = 0; flagJump = 0;
      flagra = 0; flagPC=0;
      flagrfRD1 =0; flagr30=0;
      flaghi = 0; flagr29=0;
      flaglo = 0;
      flagA = 0; flaghi2=0; flaglo2=0;
      

      case(state)
      
         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            flagJump = 0;
            flagrfRD1 = 0;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000: 
               begin            // R-format
                  case( IR[5:3] )
                     3'b001: nxt_state = EX_JR_OR_JALR; //jr,jalr
                     3'b011: nxt_state = EX_MULTU; //multu
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                  endcase
                  if(IR[5:3]==3'b010) begin
                     if(IR[2:0]==3'b000) nxt_state=EX_MFHI;
                     else if(IR[2:0]==3'b010) nxt_state=EX_MFLO;
                  end
               end

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_110,             // xori
               6'b001_111:             //lui
                  nxt_state = EX_ALU_I;

               6'b100_011:             //lw
                  nxt_state = EX_LW_1;

               6'b101_011:             //sw
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:             //beq&bne
                  nxt_state = EX_BRA_1;
               
               6'b000_010:             //j
                  nxt_state = EX_JUMP; 

               6'b000_011:             //jal
                  nxt_state = EX_JAL;  

               // rest of instructiones should be decoded here

            endcase
         end

         EX_ALU_R: begin
            //. . . . .
            aluSelA=1;
            aluSelB=2'b00;
            RegDst=1;
            MemtoReg=0;
            RFwrt=1;
            PrepareFetch;
            case(IR[5:3])
            3'b100:
            begin
               case(IR[2:0])
               3'b000: //add
               begin 
                  aluOp = `ADD;
               end
               3'b001: //addu
               begin
                  aluOp = `ADD;
               end
               3'b010: //sub
               begin
                  aluOp = `SUB;
               end
               3'b011: //subu
               begin
                  aluOp = `SUB;
               end
               3'b100: //and
               begin
                  aluOp = `AND;
               end
               3'b101: //or
               begin
                  aluOp = `OR;
               end 
               3'b110: //xor
               begin
                  aluOp = `XOR;
               end              
               3'b111: //nor
               begin
                  aluOp = `NOR;
               end
               endcase 
            end
            3'b101:
            begin
               case(IR[2:0])
               3'b010: //slt
               begin
                  aluOp = `SLT;
               end
               3'b011:
               begin //sltu
                  aluOp = `SLTU;
               end
               endcase
            end
            endcase

            end

//****
         EX_ALU_I: begin
            //. . . . .
            aluSelA=1;
            aluSelB=2'b10;
            RegDst=0;
            MemtoReg=0;
            RFwrt=1;
            PrepareFetch;
            case(IR[31:26])
               6'b001_000: //addi
               begin
                  SgnExt=1;
                  aluOp=`ADD;
               end
               6'b001_001: //addiu
               begin
                  SgnExt=0;
                  aluOp=`ADD;
               end 
               6'b001_010: //slti
               begin
                  SgnExt=1;
                  aluOp=`SLT;
               end   
               6'b001_011: //sltiu
               begin
                  SgnExt=0;
                  aluOp=`SLTU;
               end 
               6'b001_100: //andi
               begin
                  SgnExt=0;
                  aluOp=`AND;
               end   
               6'b001_101: //ori
               begin
                  SgnExt=0;
                  aluOp=`OR;
               end
               6'b001_110: //xori
               begin
                  SgnExt=0;
                  aluOp=`XOR;
               end
               6'b001_111: //lui
               begin
                  MemtoReg=0;
                  flagLui=1;
               end                                         
            endcase
         end
//****
         EX_LW_1: begin
            //. . . . .
            aluSelA=1;
            aluSelB=2'b10;
            SgnExt=1;
            aluOp=`ADD;
            MARwrt=1;
            IorD=1;
            setMRE=1;
            nxt_state=EX_LW_2;
         end
         //
         EX_LW_2: begin
            //. . . . .
            nxt_state=EX_LW_3;
         end   
         // 
         EX_LW_3: begin
            //. . . . .
            nxt_state=EX_LW_4;
         end    
         //
         EX_LW_4: begin
            //. . . . .
            clrMRE=1; 
            MDRwrt=1;
            nxt_state=EX_LW_5;
         end    
         //   
         EX_LW_5: begin
            //. . . . .
            RegDst=0; //20:16
            MemtoReg=1; //MDR
            RFwrt=1;
            PrepareFetch;
         end        
//****
         EX_SW_1: begin
            //. . . . .
            setMWE=1;
            aluSelA=1;
            aluSelB=2'b10;
            aluOp=`ADD;
            SgnExt=1;
            MARwrt=1;
            IorD=1;
            nxt_state=EX_SW_2;
         end
         //
         EX_SW_2: begin
             //. . . . .
            clrMWE=1;
            nxt_state=EX_SW_3;
         end
         //
         EX_SW_3: begin
            //. . . . .
            PrepareFetch;
         end
//****
         EX_BRA_1: begin
            //. . . . .
            aluSelA=1;
            aluSelB=2'b00;
            SgnExt=1;
            aluOp=`SUB;
            nxt_state=RESET;
            if ((( IR[31:26]==6'b000_100) && aluZero )||(( IR[31:26]==6'b000_101) && !aluZero )) 
               nxt_state=EX_BRA_2;
            
            else 
               PrepareFetch;
            
         end
         EX_BRA_2: begin
            //. . . . .
            aluSelA=0;
            aluSelB=2'b11; //imm<<2
            SgnExt=1;
            aluOp=`ADD;
            PCwrt=1;
            setMRE=1;
            IorD=1;
            MARwrt=1;
            nxt_state=FETCH1;
         end
//****
         EX_JUMP: begin
            //. . . . .
            PCwrt=1;
            flagJump=1;
            nxt_state=RESET;
         end
//****
         EX_JAL: begin
            //. . . . .
            PCwrt=1;
            RFwrt=1;
            flagJump=1;
            flagra=1;
            RegDst=0;
            MemtoReg=0;
            flagPC=1;
            nxt_state=RESET;
         end
//****
         EX_JR_OR_JALR: begin
            case(IR[2:0])
            000: begin //jr
               flagrfRD1=1;
               PCwrt=1;
                 nxt_state=RESET;
            end
            001: begin //jalr
               PCwrt=1;
               flagrfRD1=1; // PC <-- rs
               flagra=1;
               RegDst=0; 
               flagPC=1;
               flagJump=0;
               MemtoReg=0; // $31 <-- PC
               RFwrt=1;
               nxt_state=RESET;
            end
            endcase
         end
//****
         // EX_MFHI_OR_MFLO: begin
         //    case(IR[2:0])
         //    000: begin //MFHI
         //       nxt_state=EX_MFHI;
         //    end
         //    010: begin //MFLO
         //       nxt_state=EX_MFLO;
         //    end
         //    endcase
         // end
//****
      EX_MULTU: begin
         start=1;
         //multResult=A*B;
         nxt_state=EX_MULTU_BEGIN;
      end
//****
      EX_MULTU_BEGIN: begin
         start=0;
         if(ready)
            //tmp_hi=multResult[64:32];
            //tmp_lo=multResult[31:0];
            nxt_state=EX_MULTHI_WRT;
          else 
             nxt_state=EX_MULTU_BEGIN;
      end
//****
      EX_MULTHI_WRT: begin
         RFwrt=0;
         tmp_hi = multResult[63:32];
         nxt_state=EX_MULTLO_WRT;
      end
//****
      EX_MULTLO_WRT: begin
         RFwrt=0;
         tmp_lo = multResult[31:0];
         PrepareFetch;
      end
//****
      EX_MFHI: begin //MFHI
         RegDst=1;
         MemtoReg=0;
         flaghi=1;
         RFwrt=1;
         nxt_state=EX_MFHI_MFLO_WRT;
      end
//****
      EX_MFLO: begin //MFLO
         RegDst=1;
         MemtoReg=0;
         flaglo=1;
         RFwrt=1;
         nxt_state=EX_MFHI_MFLO_WRT;
      end
//****
      EX_MFHI_MFLO_WRT: begin
         RFwrt=0;
         PrepareFetch;
      end
//****
      // EX_MFHI_DELAY: begin
      //    nxt_state=EX_MFHI_MFLO_WRT;
      // end
//****
      // EX_MFLO_DELAY: begin
      //    nxt_state=EX_MFHI_MFLO_WRT;
      // end
//****
            endcase
         end
endmodule

//==============================================================================

module my_alu(
   input [2:0] Op,
   input [31:0] A,
   input [31:0] B,

   output [31:0] X,
   output        Z
);
   wire sub = Op != `ADD;
   wire [31:0] bb = sub ? ~B : B;
   wire [32:0] sum = A + bb + sub;
   wire sltu = ! sum[32];
   wire v = sub ? 
        ( A[31] != B[31] && A[31] != sum[31] )
      : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];
   reg [31:0] x;
   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule
//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule