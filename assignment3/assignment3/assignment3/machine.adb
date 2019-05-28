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
      if Integer(ProgramCounter'First) < (Integer(PC) + Integer(Offs)) and
        (Integer(PC) + Integer(Offs)) < Integer(ProgramCounter'Last) then
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
         if Regs(Rs1) > DataVal'First and Regs(Rs1) <= 0 then
            if Regs(Rs2) > (DataVal'First - Regs(Rs1)) and Regs(Rs2) < DataVal'Last then
               Regs(Rd) := Regs(Rs1) + Regs(Rs2);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Regs(Rs1) < DataVal'Last and Regs(Rs1) > 0 then
               if Regs(Rs2) < (DataVal'Last - Regs(Rs1)) and Regs(Rs2) > DataVal'First then
                  Regs(Rd) := Regs(Rs1) + Regs(Rs2);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               Ret := IllegalProgram;
            end if;
         end if;
   end DoAdd;


   procedure DoSub(Rd : in Reg; 
                   Rs1 : in Reg; 
                   Rs2 : in Reg;
                   Ret : out ReturnCode) is
   begin
      if Regs(Rs1) > DataVal'First and Regs(Rs1) <= 0 then
         if Regs(Rs2) > DataVal'First and Regs(Rs2) < (Regs(Rs1) + DataVal'Last) then
            Regs(Rd) := Regs(Rs1) - Regs(Rs2);
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         if Regs(Rs1) > 0 and Regs(Rs1) < DataVal'Last then
            if Regs(Rs2) > (DataVal'First + Regs(Rs1)) and Regs(Rs2) < DataVal'Last then
               Regs(Rd) := Regs(Rs1) - Regs(Rs2);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            Ret := IllegalProgram;
         end if; 
      end if;
   end DoSub;
   
   procedure DoMul(Rd : in Reg; 
                   Rs1 : in Reg; 
                   Rs2 : in Reg;
                   Ret : out ReturnCode) is
   begin
      if Regs(Rs2) >= 0 then
         if Regs(Rs1) > DataVal'First and Regs(Rs1) < DataVal'First/DataVal'Last then
            if Regs(Rs2) < DataVal'First/Regs(Rs1) then
               Regs(Rd) := Regs(Rs1) * Regs(Rs2);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Regs(Rs1) > DataVal'First/DataVal'Last and Regs(Rs1) <= 1 then
               if Regs(Rs2) < DataVal'Last then
                  Regs(Rd) := Regs(Rs1) * Regs(Rs2);
                  Ret:= Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               if Regs(Rs1) >1 and Regs(Rs1) < DataVal'Last then
                  if Regs(Rs2) < DataVal'Last/Regs(Rs1) then
                     Regs(Rd) := Regs(Rs1) * Regs(Rs2);
                     Ret:= Success;
                  else
                     Ret:= IllegalProgram;
                  end if;
               else
                  Ret := IllegalProgram;
               end if;
            end if;
         end if;
      else --Regs(Rs2)<0
         if Regs(Rs1) > DataVal'First and Regs(Rs1) < DataVal'Last/DataVal'First then
            if Regs(Rs2) > DataVal'Last/Regs(Rs1) then
               Regs(Rd) := Regs(Rs1) * Regs(Rs2);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Regs(Rs1) > DataVal'Last/DataVal'First and Regs(Rs1) <= 1 then
               if Regs(Rs2) > DataVal'First then
                  Regs(Rd) := Regs(Rs1) * Regs(Rs2);
                  Ret:= Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               if Regs(Rs1) > 1 and Regs(Rs1) < DataVal'Last then
                  if Regs(Rs2) > DataVal'First/Regs(Rs1) then
                     Regs(Rd) := Regs(Rs1) * Regs(Rs2);
                     Ret:= Success;
                  else
                     Ret:= IllegalProgram;
                  end if;
               else
                  Ret := IllegalProgram;
               end if;
            end if;
         end if;
      end if;
      
   end DoMul;
   
   procedure DoDiv(Rd : in Reg; 
                   Rs1 : in Reg; 
                   Rs2 : in Reg;
                   Ret : out ReturnCode) is
   begin
      if Regs(Rs2) /= 0 then
         if Regs(Rs1) > DataVal'First and Regs(Rs1) < DataVal'Last then
            Regs(Rd) := Regs(Rs1) / Regs(Rs2);
            Ret:= Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         Ret:= IllegalProgram;
      end if;
      
   end DoDiv;
   
   procedure DoLdr(Rd : in Reg; 
                   Rs : in Reg; 
                   Offs : in Offset;
                   Ret : out ReturnCode) is
      A : Addr;
   begin
      if Regs(Rs) >= DataVal(-Addr'Last) and Regs(Rs) <= 0 then
         if Offs <= Offset(Addr'Last) and Offs >= - Offset(Regs(Rs)) then
            A := Addr(Regs(Rs) + DataVal(Offs));
            Regs(Rd) := Memory(A);
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         if Regs(Rs) > 0 and Regs(Rs) <= DataVal(Addr'Last) then
            if Offs >= -Offset(Regs(Rs)) and Offs <= Offset(Addr'Last) - Offset(Regs(Rs)) then
               A := Addr(Regs(Rs) + DataVal(Offs));
               Regs(Rd) := Memory(A);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Regs(Rs) > DataVal(Addr'Last) and Regs(Rs) <= DataVal(Addr'Last - Addr'First) then
               if Offs >= Offset(Addr'First) and Offs <= Offset(Addr'Last) - Offset(Regs(Rs)) then
                  A := Addr(Regs(Rs) + DataVal(Offs));
                  Regs(Rd) := Memory(A);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               Ret := IllegalProgram;
            end if;
            
         end if;
      end if;
         
   end DoLdr;
   
   procedure DoStr(Ra : in Reg;
                   Offs : in Offset;
                   Rb : in Reg;
                   Ret : out ReturnCode) is
      A : Addr;  
   begin
       if Regs(Ra) >= DataVal(-Addr'Last) and Regs(Ra) <= 0 then
         if Offs <= Offset(Addr'Last) and Offs >= - Offset(Regs(Ra)) then
            A := Addr(Regs(Ra) + DataVal(Offs));
            Memory(A) := Regs(Rb);
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      else
         if Regs(Ra) > 0 and Regs(Ra) <= DataVal(Addr'Last) then
            if Offs >= -Offset(Regs(Ra)) and Offs <= Offset(Addr'Last) - Offset(Regs(Ra)) then
               A := Addr(Regs(Ra) + DataVal(Offs));
               Memory(A) := Regs(Rb);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Regs(Ra) > DataVal(Addr'Last) and Regs(Ra) <= DataVal(Addr'Last - Addr'First) then
               if Offs >= Offset(Addr'First) and Offs <= Offset(Addr'Last) - Offset(Regs(Ra)) then
                  A := Addr(Regs(Ra) + DataVal(Offs));
                  Memory(A) := Regs(Rb);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               Ret := IllegalProgram;
            end if;
            
         end if;
      end if;

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
               if Ret = Success then
                  IncPC(Ret,1);
               else
                  return;
               end if;                                              
            when SUB =>
               DoSub(Inst.SubRd,Inst.SubRs1,Inst.SubRs2,Ret);
               if Ret = Success then
                  IncPC(Ret,1);
               else
                  return;
               end if;                                              
            when MUL =>
               DoMul(Inst.MulRd,Inst.MulRs1,Inst.MulRs2,Ret);
               if Ret = Success then
                  IncPC(Ret,1);
               else
                  return;
               end if;                                              
            when DIV =>
               DoDiv(Inst.DivRd,Inst.DivRs1,Inst.DivRs2,Ret);
               if Ret = Success then
                  IncPC(Ret,1);
               else
                  return;
               end if;                                              
            when LDR =>
               DoLdr(Inst.LdrRd,Inst.LdrRs,Inst.LdrOffs,Ret);
               if Ret = Success then
                  IncPC(Ret,1);
               else
                  return;
               end if;                                              
            when STR =>
               DoStr(Inst.StrRa,Inst.StrOffs,Inst.StrRb,Ret);
               if Ret = Success then
                  IncPC(Ret,1);
               else
                  return;
               end if;                                              
            when MOV =>
               DoMov(Inst.MovRd,Inst.MovOffs,Ret);
               if Ret = Success then
                  IncPC(Ret,1);
               else
                  return;
               end if;                                              
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
      Prog()
      return True;
   end DetectInvalidBehaviour;
   
end Machine;
