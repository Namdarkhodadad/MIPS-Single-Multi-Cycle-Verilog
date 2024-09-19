`timescale 1ns/100ps

   `define ADD  3'b000
   `define SUB  3'b001
   `define SLT  3'b010
   `define SLTU 3'b011
   `define AND  3'b100
   `define XOR  3'b101
   `define OR   3'b110
   `define NOR  3'b111
   `define LUI  4'h8

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

   // Mult register
   wire [63:0] mult_product;
   reg [31:0] mult_hi;
   reg [31:0] mult_lo;
   wire ready;
   reg start;
   reg [31:0] mult_hi_write;
   reg mult_lo_write;

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
   reg SgnExt, aluSelA, MemtoReg, RegDst, IorD , jump, wrt_ra, jumpr, mfhi, mflo, lui; 

   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt && !jump && !jumpr)
         PC <= #0.1 aluResult;
      else if( PCwrt && jump && !jumpr)
         PC <= #0.1  {PC[31:28],IR[25:0],2'b00};
      else if(PCwrt && !jump && jumpr)
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

     // if( mult_hi_write ) mult_hi <= #0.1 mult_product[63:32];
     // if( mult_lo_write ) mult_lo <= #0.1 mult_product[31:0];

   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( RegDst ? IR[15:11] : (wrt_ra ? 31 : IR[20:16]) ),
      .WD( MemtoReg ? MDR : lui ? {IR[15:0],16'h0} : wrt_ra ? PC : mfhi ? mult_hi : mflo ? mult_lo : aluResult ) //TODO
   );
      multiplier multu(
      .clk( clk ),
      .start ( start ),  
      .A ( A ),
      .B ( B ),
      .Product ( mult_product ),
      .ready ( ready )
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
      EX_BRA_1 = 25, EX_BRA_2 = 26, EX_J=27 , EX_MULT = 28, EX_MFHI = 29 , EX_MFLO = 30,EX_JAL = 31, EX_JR = 32, EX_JALR = 33 , EX_MULTHI_WRT=34, EX_MULTLO_WRT=35 , EX_MF_WRT=36, EX_MULT_START=37;

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

      PCwrt = 0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;
      jump = 0; wrt_ra = 0; jumpr = 0;
      mfhi = 0; mflo = 0;
      mult_hi_write = 0;
      mult_lo_write = 0;
      lui = 0;

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
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            jump = 0;
            jumpr = 0;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b001: begin //jr jalr
                              case ( IR[2:0] )
                              3'b000: nxt_state = EX_JR;
                              3'b001: nxt_state = EX_JALR;
                              endcase
                        end 
                     3'b010: begin //mfhi mflo
                              case ( IR[2:0] )
                              3'b000: nxt_state = EX_MFHI;
                              3'b010: nxt_state = EX_MFLO;
                              endcase
                        end
                     3'b011: begin
                        start=1;
                        nxt_state = EX_MULT_START;   //multu
                     end
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_111,             // lui
               6'b001_110: nxt_state = EX_ALU_I;// xori
               6'b100_011: nxt_state = EX_LW_1;
               6'b101_011: nxt_state = EX_SW_1;
               6'b000_100,
               6'b000_101: nxt_state = EX_BRA_1;
               6'b000_010: nxt_state = EX_J; //j
               6'b000_011: nxt_state = EX_JAL; //jal

               // rest of instructiones should be decoded here
            endcase
         end

         EX_ALU_R: begin
            aluSelA = 1;
            aluSelB = 2'b00;
            RegDst = 1;
            MemtoReg = 0;
            RFwrt = 1;
            case ( IR[5:0] )
               6'b100000: aluOp = `ADD; //add
               6'b100001: aluOp = `ADD; //addu
               6'b100010: aluOp = `SUB; //sub
               6'b100011: aluOp = `SUB; //subu
               6'b100100: aluOp = `AND; //and
               6'b100101: aluOp = `OR; //or
               6'b100110: aluOp = `XOR; //xor
               6'b100111: aluOp = `NOR; //nor
               6'b101010: aluOp = `SLT; //slt
               6'b101011: aluOp = `SLTU; //sltu
            endcase

            PrepareFetch;
         end

         EX_ALU_I: begin
            aluSelA=1;
            aluSelB=2'b10;
            RegDst=0;
            MemtoReg=0;
            RFwrt=1;
            PrepareFetch;

            case ( IR[28:26] )
               3'b000: begin //addi
                   aluOp = `ADD; 
                   SgnExt = 1;
               end
               3'b001: begin //addiu
                  aluOp = `ADD;
                  SgnExt = 0;
               end
               3'b010: begin //slti
                  aluOp = `SLT;
                  SgnExt = 1;
               end
               3'b011: begin //sltiu
                  aluOp = `SLTU;
                  SgnExt = 0;
               end
               3'b100: begin //andi
                  aluOp = `AND;
                  SgnExt = 0;
               end
               3'b101: begin
                  aluOp = `OR; //ori
                  SgnExt = 0;
               end
               3'b110: begin
                  aluOp = `XOR; //xori
                  SgnExt = 0;
               end
               3'b111: //lui
               begin
                  //aluOp = `LUI; //lui
                  //SgnExt = 0;
                  lui=1;
                  MemtoReg=0;
               end
            endcase
         end

         EX_LW_1: begin
            SgnExt = 1;
            aluSelA = 1;
            aluSelB = 2'b10;
            aluOp = `ADD;
            IorD = 1;
            setMRE = 1;
            MARwrt = 1;
            nxt_state = EX_LW_2;
         end

         EX_LW_2: begin
            nxt_state = EX_LW_3;
         end

         EX_LW_3: begin
            nxt_state = EX_LW_4;
         end

         EX_LW_4: begin
            clrMRE = 1;
            MDRwrt = 1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            RegDst = 0;
            MemtoReg = 1;
            RFwrt = 1;
            PrepareFetch;
         end

         EX_SW_1: begin
            SgnExt = 1;
            aluSelA = 1;
            aluSelB = 2'b10;
            aluOp = `ADD;
            MARwrt = 1;
            IorD = 1;
            setMWE = 1;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin
            PrepareFetch;
         end

         EX_BRA_1: begin
            SgnExt = 1;
            aluSelA = 1;
            aluSelB = 2'b00;
            aluOp = `SUB;

            case (IR[26])
               1'b0: begin //beq
                  if (aluZero)
                     nxt_state = EX_BRA_2;
                  else
                     PrepareFetch;
               end

               1'b1: begin //bne
                  if (aluZero)
                     PrepareFetch;
                  else
                     nxt_state = EX_BRA_2;
               end         
            endcase

         end

         
         EX_BRA_2: begin
            SgnExt = 1;
            aluSelA = 0;
            aluSelB = 2'b11;
            aluOp = `ADD;
            IorD = 1;
            PCwrt = 1;
            setMRE = 1;
            MARwrt = 1;
            nxt_state = FETCH1;
         end
         EX_MULT_START: begin
            start=1;
            nxt_state=EX_MULT;
         end
         EX_MULT: begin
            start=0;
            if(!ready)
               nxt_state = EX_MULT;
               
            else begin
              // mult_hi_write = 1;
              // mult_lo_write = 1;
               nxt_state = EX_MULTHI_WRT;
              // PrepareFetch;
            end
         end
         EX_MULTHI_WRT: begin
         RFwrt=0;
         mult_hi = mult_product[63:32];
         nxt_state=EX_MULTLO_WRT;
      end
        EX_MULTLO_WRT: begin
         RFwrt=0;
         mult_lo = mult_product[31:0];
         PrepareFetch;
      end

         EX_MFHI: begin
            RFwrt=1;
            RegDst=1;
            MemtoReg=0;
            mfhi = 1;
            nxt_state= EX_MF_WRT;
           end
         EX_MFLO: begin
            RFwrt=1;
            RegDst=1;
            MemtoReg=0;
            mflo = 1;
            nxt_state= EX_MF_WRT;
           end

         EX_MF_WRT: begin
            RFwrt=0;
            PrepareFetch;
         end

         EX_J: begin
            PCwrt=1;
            jump=1;
            nxt_state=RESET;
         end

         EX_JAL: begin
            PCwrt=1;
            RFwrt = 1;
            jump = 1;
            RegDst=0;
            MemtoReg=0;
            wrt_ra=1;
            nxt_state=RESET;
         end

         EX_JR: begin
            PCwrt=1;
            nxt_state=RESET;
            jumpr = 1;
         end

         EX_JALR: begin
            PCwrt=1;
            RegDst=0;
            MemtoReg=0;
            RFwrt=1;
            wrt_ra=1;
            jumpr = 1;
            jump=0;
            nxt_state=RESET;
         end
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
         //`LUI : x = {B[15:0], 16'h0};
         //`MULT : x = mult_product;
         //`MFHI : x =  mult_hi;
         //`MFLO : x =  mult_lo;
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

//==============================================================================
//Multu
module multiplier(
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );
reg [31:0] Multiplicand ;
reg [31:0]  Multiplier;
reg [8:0]  counter;
wire product_write_enable;
wire [32:0] adder_output;
assign adder_output = Product + Multiplicand;
assign product_write_enable = Multiplier[0];
assign ready = counter[8];
always @ (posedge clk)

   if(start) begin
      counter <= 8'h0 ;
      Multiplier <= B;
      Product <= 64'h00;
      Multiplicand <= {32'h00, A} ;
   end
   else if(! ready ) begin
         counter <= counter + 1;
         Product <= Product >> 1;

      if(product_write_enable) begin
         Product <= adder_output;
         end
   end   

endmodule