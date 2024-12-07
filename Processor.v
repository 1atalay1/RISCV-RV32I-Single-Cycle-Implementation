`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: Osman Gazi ATALAY
// 
// Create Date: 25.11.2024 18:42:38
// Design Name: 
// Module Name: Processor
// Project Name: Single Cycle Processor
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module Processor(
        input clk
    );
     wire[31:0] current_address;
     wire [31:0] next_instruction_address;
     wire [31:0] current_instruction;
     wire isZero,PC_src, Mem_Write_Enable,ALU_src,Reg_Write_Enable;
     wire[1:0] Immediate_src, Result_src;
     wire[2:0] ALU_control;
     PC Program_Counter(clk,next_instruction_address,current_address);
     Instruciton_Mem Instruction_Memory(current_address,current_instruction);
    
     
     
     Control_Unit Control(
                          current_instruction,isZero,PC_src,
                            Mem_Write_Enable,ALU_src,Reg_Write_Enable,
                          Immediate_src,Result_src ,ALU_control
                          );
                          
                          
    wire [11:0] I_immediate= current_instruction[31:20];
    wire [11:0] S_immediate = {current_instruction[31:25],current_instruction[11:7]};
    wire [11:0] B_immediate ={current_instruction[31],current_instruction[7],current_instruction[30:25],current_instruction[11:8]};
    wire [19:0] J_immediate = {current_instruction[31],current_instruction[19:12],current_instruction[20],current_instruction[30:21]};
    wire [31:0] current_immediate;
    Sign_Extend_Unit Sign_Extend(I_immediate,S_immediate,B_immediate,J_immediate,Immediate_src,current_immediate);
    wire [31:0] sequential_PC;
    wire [31:0]  branch_PC;                
    PC_Plus_4 PC_increment_4(current_address,sequential_PC);
    PC_Plus_Target_Address PC_increment_Target_Adress (current_address,current_immediate,branch_PC);
    Mux2_X_1 PC_Mux(PC_src,sequential_PC,branch_PC,next_instruction_address);
    
    wire [4:0] source_reg1=current_instruction[19:15];
    wire [4:0] source_reg2=current_instruction[24:20];
    wire [4:0] destination_reg=current_instruction[11:7];
    wire [31:0] reg1_data,reg2_data;
    wire[31:0] ALU_Result,MEM_Result,Register_File_Read_Data; 
    Mux4_X_1 Register_File_Mux(Result_src,ALU_Result,MEM_Result,sequential_PC,Register_File_Read_Data);
    Register_File Register_Unit (clk,Reg_Write_Enable,source_reg1,source_reg2,destination_reg,Register_File_Read_Data,reg1_data,reg2_data);
    
   
   wire [31:0] current_ALU_source2;
   Mux2_X_1 ALU_Src_Mux(ALU_src,reg2_data,current_immediate,current_ALU_source2);
   wire Negative_Flag, OverFlow_Flag, Carry_Flag;
   ALU ALU_Unit(reg1_data,current_ALU_source2,ALU_control,isZero,Negative_Flag, OverFlow_Flag, Carry_Flag,ALU_Result);
   Data_Mem Data_Memory (clk,Mem_Write_Enable,ALU_Result,reg2_data,MEM_Result);
   
    
    
    
endmodule
module PC (
        input clk,
        input [31:0] next_instruction_adress,
        output reg [31:0] current_instruction_adress
);
    initial begin 
        current_instruction_adress=32'b0;
    end

    always @(posedge clk)begin 
        current_instruction_adress<=next_instruction_adress;
    end
endmodule

module PC_Plus_4(
        input [31:0] Program_Counter,
        output reg[31:0] new_Program_Counter

);
localparam MAX_ADDRESS=4294967295;
wire [32:0] temp;
Carry_Look_Ahead_Adder #(32,8) adder(Program_Counter,32'h00000004,temp);
    always @(*) begin 
        if (Program_Counter+3<=MAX_ADDRESS && (Program_Counter[31]==temp[31] &&(Program_Counter[31]==1'b0))) new_Program_Counter=temp;
        else new_Program_Counter=32'd0;
    end
endmodule

module PC_Plus_Target_Address(
        input [31:0] Program_Counter,
        input  [31:0] Target,
        output [31:0] new_Program_Counter
);
wire [32:0] temp;
localparam MAX_ADDRESS=4294967295;
Carry_Look_Ahead_Adder #(32,8) adder(Program_Counter,Target,temp);
    assign new_Program_Counter= ((temp+3<=MAX_ADDRESS) &&(Program_Counter[31]==temp[31] &&(Program_Counter[31]==Target[31]))) ? temp[31:0] : 32'd0;
endmodule

module Instruciton_Mem(
            input[31:0] instruction_adress,
            output reg[31:0] instruction
); 
    
    reg [7:0] Instruction_Cells[4294967295:0];
    localparam MAX_ADDRESS=4294967295;
    initial begin 
        // Adding Instructions... Sample Instructions
    /*
   addi x1, x0, 4        # x1 = 4
    addi x2, x0, 8        # x2 = 8
    add x3, x1, x2        # x3 = x1 + x2
    sll x4, x3, x1        # x4 = x3 << x1
    lw x5, 0(x1)          # x5 = Mem[x1]
    sw x6, 4(x2)          # Mem[x2+4] = x6
    beq x1, x2, label     # if x1 == x2 jump to label
    jal x7, label         # jump to label and store return address in x7

label:
    */
    {Instruction_Cells[3],Instruction_Cells[2],Instruction_Cells[1],Instruction_Cells[0]}=32'h00430313;
    {Instruction_Cells[7],Instruction_Cells[6],Instruction_Cells[5],Instruction_Cells[4]}=32'h00830393;
    {Instruction_Cells[11],Instruction_Cells[10],Instruction_Cells[9],Instruction_Cells[8]}=32'h00C30333;
    {Instruction_Cells[15],Instruction_Cells[14],Instruction_Cells[13],Instruction_Cells[12]}=32'h004303B3;
    {Instruction_Cells[19],Instruction_Cells[18],Instruction_Cells[17],Instruction_Cells[16]}=32'h00030383;
    {Instruction_Cells[23],Instruction_Cells[22],Instruction_Cells[21],Instruction_Cells[20]}=32'h00430323;
    {Instruction_Cells[27],Instruction_Cells[26],Instruction_Cells[25],Instruction_Cells[24]}=32'h00030363;
    {Instruction_Cells[31],Instruction_Cells[30],Instruction_Cells[29],Instruction_Cells[28]}=32'h000303F6;     
    end
    
        always @ (*) begin 
        //Little Endian
                if ((instruction_adress%4==0) &&(instruction_adress+3<=MAX_ADDRESS))begin 
                    instruction={Instruction_Cells[instruction_adress+3],
                    Instruction_Cells[instruction_adress+2],
                    Instruction_Cells[instruction_adress+1],
                    Instruction_Cells[instruction_adress]};
                end
        end



endmodule

module Control_Unit(
      input [31:0] instruction,input isZero,
      output reg PC_src, Mem_Write_Enable,ALU_src,Reg_Write_Enable,
      output reg[1:0] Immediate_src, Result_src,
      output reg [2:0] ALU_control
);

        always @(*) begin 
             if (instruction[6:0]==7'b0110011) begin
                //R TYPE
                PC_src=1'b0; // PC+4
                Result_src= 2'b00; //receives result from ALU
                Mem_Write_Enable=1'b0;
                ALU_src=1'b0; // Takes two register operand
                Immediate_src=2'bxx;
                Reg_Write_Enable=1'b1;
                    case ({instruction[31:25],instruction[14:12]}) 
                   10'b0000000_000: ALU_control=3'd0; //Add 
                   10'b0100000_000: ALU_control=3'd1; //Sub
                   10'b0000000_111: ALU_control=3'd2; //And
                   10'b0000000_110: ALU_control=3'd3; //Or
                   10'b0000000_001: ALU_control=3'd4; //LSL
                    endcase 
                end
             else if (instruction[6:0]==7'b00x0011) begin
                //I Type
                case (instruction[14:12]) 
                    3'b010: begin 
                        //Load (LW)
                        PC_src=1'b0; // PC+4
                        Result_src= 2'b01; //receives result from Memory
                        Mem_Write_Enable=1'b0;
                        ALU_src=1'b1; // Takes one immedaite operator
                        Immediate_src=2'b00;
                        Reg_Write_Enable=1'b1;
                    end
                    3'b000: begin 
                        //Addi
                        PC_src=1'b0; // PC+4
                        Result_src= 2'b00; //receives result from ALU
                        Mem_Write_Enable=1'b0;
                        ALU_src=1'b1; // Takes one immedaite operator
                        Immediate_src=2'b00;
                        Reg_Write_Enable=1'b1;
                    end
                endcase
                         ALU_control=3'd0; //Addition 
             end
               else if (instruction[6:0]==7'b0100011) begin 
                        //S Type (Store)
                        PC_src=1'b0; // PC+4
                        Result_src= 2'bxx; //Do not write into register file
                        Mem_Write_Enable=1'b1;
                        ALU_src=1'b1; // Takes one immedaite operator
                        Immediate_src=2'b01;
                        Reg_Write_Enable=1'b0;
                        ALU_control=3'd0;//Addition
               end
                else if (instruction[6:0]==7'b1100011) begin 
                    //B Type (Beq)
                        PC_src=isZero; // if ALU's isZero flag is zero then branch 
                        Result_src= 2'bxx; //Do not write into register file
                        Mem_Write_Enable=1'b0;
                        ALU_src=1'b0; // Takes two register as operand
                        Immediate_src=2'b10;
                        Reg_Write_Enable=1'b0;
                        ALU_control=3'd1;//Subtraction
                end
                
                else if (instruction[6:0]==7'b1101111) begin
                    //J Type (JAL)
                        PC_src=1'b1; // Branch
                        Result_src= 2'b10; //Write register File PC+4
                        Mem_Write_Enable=1'b0;
                        ALU_src=1'bx; 
                        Immediate_src=2'b11;
                        Reg_Write_Enable=1'b1;
                        ALU_control=3'bxxx;
                    end
             end
               
      
endmodule


module Register_File(
    input clk,write_enable,
    input[4:0] source_reg1,source_reg2,destination_reg,
    input[31:0] write_data,
    output reg [31:0] reg1_data,reg2_data
);
      reg [31:0] registers [31:0];
       integer i;
      initial begin
    for (i = 0; i < 32; i = i + 1) begin
        registers[i] = 32'h00000000;
        end
    end

      always @(*) begin 
         reg1_data=registers[source_reg1];
         reg2_data=registers[source_reg2];
      end
      always @(posedge clk) begin 
        if (write_enable)begin
            if(destination_reg!=5'd0) begin 
                registers[destination_reg]<=write_data;
            end
        
         end
      
      end


endmodule

module ALU (
    input [31:0] operand1,operand2,
    input [2:0] ALU_control,
    output reg zero_Flag,Negative,
    output OverFlow,Carry,
    output reg [31:0] result
);
    /*
        000:addition
        001:subtraction
        010:AND
        011:OR
        100:LSL
    */
    
   wire [32:0] temp;
   Carry_Look_Ahead_Adder #(32,8) adder(operand1,operand2,temp);
   wire over_flow_temp,over_flow_temp_2,over_flow_temp_not;
   nor(over_flow_temp,operand1[31],operand2[31],ALU_control[0]);
   not (over_flow_temp_not,over_flow_temp);
   xor (over_flow_temp_2,temp[31],operand1[31]);
   and (OverFlow,over_flow_temp_not,over_flow_temp_2,~ALU_control[1]);
   and(Carry,~ALU_control[1],temp[32]);
  

    always @(*) begin
            
            case (ALU_control)
                3'b000: begin 
                    result=temp[31:0];
                end
                3'b001: begin
                    result=temp[31:0];
                 end
                3'b010: begin 
                    result=operand1 & operand2;
                end
                3'b011: begin 
                    result=operand1 | operand2;    
                end
                3'b100: begin 
                    result=operand1<<operand2;
                end
            endcase
            if(result==32'd0) zero_Flag=1'b1;
            else zero_Flag=1'b0;
            Negative=result[31];
    end

endmodule

module Data_Mem(
    input clk,write_enable,
    input[31:0] adress,write_data,
    output reg[31:0] read_data 
);
        reg [7:0] Mem_Cell [4294967295:0];
        localparam MAX_ADDRESS=4294967295;
        
        initial begin 
        // Below Datas are arbittary value for running program.
        {Mem_Cell[3],Mem_Cell[2],Mem_Cell[1],Mem_Cell[0]}=32'd5;
        {Mem_Cell[7],Mem_Cell[6],Mem_Cell[5],Mem_Cell[4]}=32'd42;
        {Mem_Cell[11],Mem_Cell[10],Mem_Cell[9],Mem_Cell[8]}=32'd12;
        {Mem_Cell[15],Mem_Cell[14],Mem_Cell[13],Mem_Cell[12]}=32'd24;
        {Mem_Cell[19],Mem_Cell[18],Mem_Cell[17],Mem_Cell[16]}=32'd1;
        
        end
        
        always @(*) begin 
        //Little Endian
         if (adress + 3 <= MAX_ADDRESS) begin
            read_data={Mem_Cell[adress+3],Mem_Cell[adress+2],Mem_Cell[adress+1],Mem_Cell[adress+0]};
            end
            else read_data<=32'd0;
        end
        always @(posedge clk) begin
        //Little Endian 
            if(write_enable) begin
                    if((adress + 3 <= MAX_ADDRESS) && (adress % 4 == 0)) begin 
                            Mem_Cell[adress]<=write_data[7:0];
                            Mem_Cell[adress+1]<=write_data[15:8];
                            Mem_Cell[adress+2]<=write_data[23:16];
                            Mem_Cell[adress+3]<=write_data[31:24];
                    end
             end
            
        end
 endmodule

module Sign_Extend_Unit(
            input [11:0]  I_immediate,S_immediate,B_immediate,
            input [19:0]  J_immediate,
            input [1:0]  select_bit,
            output reg [31:0] immediate_value
            
);
            /*select bit 
                00= I type
                01: S type
                10: B type
                11: J type
            */
            always @(*) begin 
                case(select_bit)
                2'b00:  immediate_value = { {20{I_immediate[11]}}, I_immediate };
                2'b01:  immediate_value = { {20{S_immediate[11]}}, S_immediate };
                2'b10:  immediate_value = { {19{B_immediate[11]}}, B_immediate,1'b0 };   
                2'b11:  immediate_value = { {11{J_immediate[19]}}, J_immediate,1'b0 };              
                 endcase
            end
            

endmodule

module Mux2_X_1 (
        input select_bit,
        input [31:0] source0,source1,
        output [31:0] result
);
assign result =(select_bit) ? source1:source0;
endmodule

module Mux4_X_1(
    input [1:0] select_bit,
    input [31:0] source0,source1,source2,
    output reg [31:0] result
);
    //00 --> ALU result
    //01 --> Memory Result
    //10 --> PC+4;
    always @(*) begin 
        case(select_bit) 
        2'b00 : result=source0;
        2'b01: result=source1;
        2'b1x: result=source2;
        endcase
    end

endmodule


module Carry_Look_Ahead_Adder  #(parameter N=16,M=4) (  //2^n bit adder    M= 2^n / 4 
            input [N-1:0] a, b,
            output[N:0] sum
    );
    generate 
    genvar i;
    wire [M-1:0] carry_holder;
    for (i=0;i<=M;i=i+1) begin 
      localparam integer min_index = 4*i;
      localparam integer max_index = min_index +3 ;
            if(i==0) begin
        four_bit_Full_Adder adder (a[max_index:min_index],b[max_index:min_index],1'b0,carry_holder[i],sum[max_index:min_index]);
            end
            else begin 
            four_bit_Full_Adder adder (a[max_index:min_index],b[max_index:min_index],carry_holder[i-1],carry_holder[i],sum[max_index:min_index]);
            end
       end
    endgenerate
    assign sum[N]= carry_holder[M-1];

endmodule
module Full_Adder(
    input a, b, carry_in,
    output reg sum, 
    output reg carry_out
);
    always @(*) begin 
        case ({a, b, carry_in}) 
            3'b000: begin
                sum = 1'b0;
                carry_out = 1'b0;
            end
            3'b001: begin
                sum = 1'b1;
                carry_out = 1'b0;
            end
            3'b010: begin
                sum = 1'b1;
                carry_out = 1'b0;
            end
            3'b011: begin
                sum = 1'b0;
                carry_out = 1'b1;
            end
            3'b100: begin
                sum = 1'b1;
                carry_out = 1'b0;
            end
            3'b101: begin
                sum = 1'b0;
                carry_out = 1'b1;
            end
            3'b110: begin
                sum = 1'b0;
                carry_out = 1'b1;
            end
            3'b111: begin
                sum = 1'b1;
                carry_out = 1'b1;
            end
            default: begin
                sum = 1'b0;       
                carry_out = 1'b0; 
            end
        endcase
    end
endmodule

module four_bit_Full_Adder(
    input [3:0] a, b,
    input carry_in,
    output carry_out, 
    output [3:0] sum 
);
    wire g0, g1, g2, g3, p0, p1, p2, p3 , c0, c1, c2;     

  
    assign g0 = a[0] & b[0];
    assign p0 = a[0] ^ b[0];
    assign c0 = g0 | (p0 & carry_in);
    
    assign g1 = a[1] & b[1];
    assign p1 = a[1] ^ b[1];
    assign c1 = g1 | (p1 & c0);
    
    assign g2 = a[2] & b[2];
    assign p2 = a[2] ^ b[2];
    assign c2 = g2 | (p2 & c1);
    
    assign g3 = a[3] & b[3];
    assign p3 = a[3] ^ b[3];
    assign carry_out = g3 | (p3 & c2);

   
    wire [3:0] carry_array = {c2, c1, c0, carry_in};
    wire dummy; 
    

    generate 
        genvar i;
        for (i = 0; i < 4; i = i + 1) begin : addition
            Full_Adder temp ((a[i]),(b[i]),(carry_array[i]), (sum[i]), (dummy));
        end
    endgenerate 
endmodule

