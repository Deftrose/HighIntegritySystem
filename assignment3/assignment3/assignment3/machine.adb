with Instruction;
use Instruction;
with Debug; use Debug;

-- used so we can print TAB character
with Ada.Characters.Latin_1;

package body Machine with SPARK_Mode is
   -- data values are 32-bit integers
   -- this is the type of words used in the virtual machine
   type DataVal is range -(2**31) .. +(2**31 - 1);
      
   -- the registers
   Regs : array (Reg) of DataVal := (others => 0);
   
   -- the memory
   Memory : array (Addr) of DataVal := (others => 0);
   
   -- the program counter
   PC : ProgramCounter := ProgramCounter'First;
      
   procedure IncPC(Ret : out ReturnCode; Offs : in Offset) is
   begin
      if 0 < (Integer(PC) + Integer(Offs)) and
        (Integer(PC) + Integer(Offs)) < MAX_PROGRAM_LENGTH then
        PC := ProgramCounter(Integer(PC) + Integer(Offs));
        Ret := Success;
      else
        Ret := IllegalProgram;
      end if;
   end IncPC;
   
   procedure DoAdd(Rd : in Reg; 
                   Rs1 : in Reg; 
                   Rs2 : in Reg;
                   Ret : out ReturnCode) is
   begin
      if Regs(Rs1) < DataVal(Offset'Last) and Regs(Rs2) < DataVal(Offset'Last) 
        and Regs(Rs1) > DataVal(Offset'First) and Regs(Rs2) > DataVal(Offset'First)
      then
         if (Regs(Rs1) + Regs(Rs2)) > DataVal(Offset'First) and
           (Regs(Rs1) + Regs(Rs2)) < DataVal(Offset'Last) then
         Regs(Rd) := Regs(Rs1) + Regs(Rs2);
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         Ret := IllegalProgram;
         end if;
   end DoAdd;


   procedure DoSub(Rd : in Reg; 
                   Rs1 : in Reg; 
                   Rs2 : in Reg;
                   Ret : out ReturnCode) is
   begin
      if Regs(Rs1) > DataVal(Offset'First) and Regs(Rs1) < DataVal(Offset'Last)
        and Regs(Rs2) < -DataVal(Offset'First) and Regs(Rs2) > -DataVal(Offset'Last) then
         if (Regs(Rs1) - Regs(Rs2)) > DataVal(Offset'First) and 
           (Regs(Rs1) - Regs(Rs2)) < DataVal(Offset'Last) then
            Regs(Rd) := Regs(Rs1) - Regs(Rs2);
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         Ret := IllegalProgram;
      end if;
   end DoSub;
   
   procedure DoMul(Rd : in Reg; 
                   Rs1 : in Reg; 
                   Rs2 : in Reg;
                   Ret : out ReturnCode) is
   begin
      if Regs(Rs1) > DataVal(-2**31/Integer(Offset'Last)) and Regs(Rs1) < DataVal((2**31-1)/Integer(Offset'Last))
        and Regs(Rs2) < DataVal(Offset'Last) and Regs(Rs2) > DataVal(Offset'First) then
         Regs(Rd) := Regs(Rs1) * Regs(Rs2);
         Ret := Success;
      else
         if Regs(Rs1) /= 0 then
            if Regs(Rs1) > DataVal((2**31-1)/Integer(Offset'Last)) and Regs(Rs1) < DataVal(Offset'Last) then
              if Regs(Rs2) > DataVal(-2**31)/Regs(Rs1) and Regs(Rs2) < DataVal(2**31-1)/Regs(Rs1) then
                  Regs(Rd) := Regs(Rs1)*Regs(Rs2);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
              end if;
            else
               if Regs(Rs1) < DataVal(-2**31/Integer(Offset'Last)) and Regs(Rs1) > DataVal(Offset'First) then
                 if Regs(Rs2) > DataVal(2**31-1)/Regs(Rs1) and Regs(Rs2) < DataVal(-2**31)/Regs(Rs1) then
                  Regs(Rd) := Regs(Rs1)*Regs(Rs2);
                     Ret := Success;
                  else
                     Ret := IllegalProgram;
                     end if;
               else
                  Ret:= IllegalProgram;
               end if;
            end if;
         else
            Ret := IllegalProgram;
         end if;
      end if;
   end DoMul;
   
   procedure DoDiv(Rd : in Reg; 
                   Rs1 : in Reg; 
                   Rs2 : in Reg;
                   Ret : out ReturnCode) is
   begin
      if Regs(Rs2) /= 0 then
         if Regs(Rs1) > DataVal(Offset'First) and Regs(Rs1) < DataVal(Offset'Last) 
           and Regs(Rs2) > DataVal(Offset'First) and Regs(Rs2) < DataVal(Offset'Last) then
            Regs(Rd) := Regs(Rs1) / Regs(Rs2);
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         Ret := IllegalProgram;
      end if;
   end DoDiv;
   
   procedure DoLdr(Rd : in Reg; 
                   Rs : in Reg; 
                   Offs : in Offset;
                   Ret : out ReturnCode) is
      A : Addr;
      begin
      if Regs(Rs) > DataVal(-Integer(MEMORY_SIZE-1)) and Regs(Rs) < DataVal(Offset'Last) then
         if (Regs(Rs) + DataVal(Offs)) >= 0
           and (Regs(Rs) + DataVal(Offs)) <= DataVal(MEMORY_SIZE-1) then
            A := Addr(Regs(Rs) + DataVal(Offs));
            Regs(Rd) := Memory(A);
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         Ret := IllegalProgram;
      end if;
      Ret := IllegalProgram;
   end DoLdr;
   
   procedure DoStr(Ra : in Reg;
                   Offs : in Offset;
                   Rb : in Reg;
                   Ret : out ReturnCode) is
      A : Addr := Addr(Regs(Ra) + DataVal(Offs));   
   begin
      Memory(A) := Regs(Rb);
      Ret := Success;
   end DoStr;
   
   procedure DoMov(Rd : in Reg;
                   Offs : in Offset;
                   Ret : out ReturnCode) is
   begin
      Regs(Rd) := DataVal(Offs);
      Ret := Success;
   end DoMov;
   
   procedure ExecuteProgram(Prog : in Program;
                            Cycles : in Integer;
                            Ret : out ReturnCode;
                            Result : out Integer) 
   is
      CycleCount : Integer := 0;
      Inst : Instr;
   begin
      Ret := Success;
      PC := ProgramCounter'First;
      Result := 0;
      while (CycleCount < Cycles and Ret = Success) loop
         Inst := Prog(PC);
         
         -- debug print pc and current instruction
         Put(Integer(PC)); Put(':'); Put(Ada.Characters.Latin_1.HT);
         DebugPrintInstr(Inst);
         New_Line;
         
         case Inst.Op is
            when ADD =>
               DoAdd(Inst.AddRd,Inst.AddRs1,Inst.AddRs2,Ret);
               IncPC(Ret,1);
            when SUB =>
               DoSub(Inst.SubRd,Inst.SubRs1,Inst.SubRs2,Ret);
               IncPC(Ret,1);
            when MUL =>
               DoMul(Inst.MulRd,Inst.MulRs1,Inst.MulRs2,Ret);
               IncPC(Ret,1);
            when DIV =>
               DoDiv(Inst.DivRd,Inst.DivRs1,Inst.DivRs2,Ret);
               IncPC(Ret,1);
            when LDR =>
               DoLdr(Inst.LdrRd,Inst.LdrRs,Inst.LdrOffs,Ret);
               IncPC(Ret,1);
            when STR =>
               DoStr(Inst.StrRa,Inst.StrOffs,Inst.StrRb,Ret);
               IncPC(Ret,1);
            when MOV =>
               DoMov(Inst.MovRd,Inst.MovOffs,Ret);
               IncPC(Ret,1);
            when Instruction.RET =>
               Result := Integer(Regs(Inst.RetRs));
               Ret := Success;
               return;
            when JMP =>
               IncPC(Ret,Inst.JmpOffs);
            when JZ =>
               if Regs(Inst.JzRa) = 0 then
                  IncPC(Ret,Inst.JzOffs);
               else
                  IncPc(Ret,1);
               end if;
            when NOP =>
               IncPC(Ret,1);
         end case;
         CycleCount := CycleCount + 1;
      end loop;
      if Ret = Success then
         -- Cycles instructions executed without a RET or invalid behaviour
         Ret := CyclesExhausted;
      end if;
   end ExecuteProgram;

   function DetectInvalidBehaviour(Prog : in Program;
                                   Cycles : in Integer) return Boolean is
   begin
      return True;
   end DetectInvalidBehaviour;
   
end Machine;
