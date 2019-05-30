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
      
      -- This array is used to mark if the register is assigned with value
      -- If the register hasn't been assigned, using it will be regard as invalid
      RegsSigned : array (Reg) of Boolean := ( others => False);
      
      -- This array is used to mark if the memory is assigned with value
      -- If this memory hasn't been assigned value, it should not be used
      MemorySigned : array (Addr) of Boolean := ( others => False);
      
      -- Registers used to store the value of used register
      Check_Regs : array (Reg) of DataVal := (others => 0);
      
      -- Memory used to store the value of memory
      Check_Memory : array (Addr) of DataVal := ( others => 0);
      
      -- Program counter
      Check_PC : ProgramCounter := ProgramCounter'First;
      
      -- If the instruction is valid
      Ret : ReturnCode := Success;
      
      -- the cycle counter
      CycleCount : Integer := 0 ;
      -- the instruction 
      Inst : Instr;
      
      -- Increasse the PC
      procedure Check_InCPC(Ret : out ReturnCode; Offs : in Offset) is
      begin
         -- the value should not be out of Program range
         if Integer(ProgramCounter'First) < (Integer(Check_PC) + Integer(Offs)) and
           (Integer(Check_PC) + Integer(Offs)) < Integer(ProgramCounter'Last) then
            Check_PC := ProgramCounter(Integer(Check_PC) + Integer(Offs));
            Ret := Success;
         else
            Ret := IllegalProgram;
         end if;
      end Check_InCPC;
      
      -- Check if the instruction add is valid
      procedure CheckAdd(Rd : in Reg; 
                         Rs1 : in Reg; 
                         Rs2 : in Reg;
                         Ret : out ReturnCode) is
      begin -- The sum of these two value should not out of range
         if Check_Regs(Rs1) > DataVal'First and Check_Regs(Rs1) <= 0 then
            if Check_Regs(Rs2) > (DataVal'First - Check_Regs(Rs1)) and Check_Regs(Rs2) < DataVal'Last then
               Check_Regs(Rd) := Check_Regs(Rs1) + Check_Regs(Rs2);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Check_Regs(Rs1) < DataVal'Last and Check_Regs(Rs1) > 0 then
               if Check_Regs(Rs2) < (DataVal'Last - Check_Regs(Rs1)) and Check_Regs(Rs2) > DataVal'First then
                  Check_Regs(Rd) := Check_Regs(Rs1) + Check_Regs(Rs2);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               Ret := IllegalProgram;
            end if;
         end if;
      end CheckAdd;   
 
      -- Check if the instruction sub is valid
      procedure CheckSub(Rd : in Reg; 
                         Rs1 : in Reg; 
                         Rs2 : in Reg;
                         Ret : out ReturnCode) is
      begin -- Check_Regs(Rs1) - Check_Regs(Rs2) should not out of range
         if Check_Regs(Rs1) > DataVal'First and Check_Regs(Rs1) <= 0 then
            if Check_Regs(Rs2) > DataVal'First and Check_Regs(Rs2) < (Check_Regs(Rs1) + DataVal'Last) then
               Check_Regs(Rd) := Check_Regs(Rs1) - Check_Regs(Rs2);
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Check_Regs(Rs1) > 0 and Check_Regs(Rs1) < DataVal'Last then
               if Check_Regs(Rs2) > (DataVal'First + Check_Regs(Rs1)) and Check_Regs(Rs2) < DataVal'Last then
                  Check_Regs(Rd) := Check_Regs(Rs1) - Check_Regs(Rs2);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               Ret := IllegalProgram;
            end if; 
         end if;
      end CheckSub;
   
      -- Check if the instruction mul is valid
      procedure CheckMul(Rd : in Reg; 
                         Rs1 : in Reg; 
                         Rs2 : in Reg;
                         Ret : out ReturnCode) is
      begin -- Check_Regs(Rs1) * Check_Regs(Rs2)should not out of range of dataValue
         if Check_Regs(Rs2) >= 0 then
            if Check_Regs(Rs1) > DataVal'First and Check_Regs(Rs1) < DataVal'First/DataVal'Last then
               if Check_Regs(Rs2) < DataVal'First/ Check_Regs(Rs1) then
                  Check_Regs(Rd) := Check_Regs(Rs1) * Check_Regs(Rs2);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               if Check_Regs(Rs1) > DataVal'First/DataVal'Last and Check_Regs(Rs1) <= 1 then
                  if Check_Regs(Rs2) < DataVal'Last then
                     Check_Regs(Rd) := Check_Regs(Rs1) * Check_Regs(Rs2);
                     Ret:= Success;
                  else
                     Ret := IllegalProgram;
                  end if;
               else
                  if Check_Regs(Rs1) >1 and Check_Regs(Rs1) < DataVal'Last then
                     if Check_Regs(Rs2) < DataVal'Last/ Check_Regs(Rs1) then
                        Check_Regs(Rd) := Check_Regs(Rs1) * Check_Regs(Rs2);
                        Ret:= Success;
                     else
                        Ret:= IllegalProgram;
                     end if;
                  else
                     Ret := IllegalProgram;
                  end if;
               end if;
            end if;
         else --Check_Regs(Rs2)<0
            if Check_Regs(Rs1) > DataVal'First and Check_Regs(Rs1) < DataVal'Last/DataVal'First then
               if Check_Regs(Rs2) > DataVal'Last/Check_Regs(Rs1) then
                  Check_Regs(Rd) := Check_Regs(Rs1) * Check_Regs(Rs2);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               if Check_Regs(Rs1) > DataVal'Last/DataVal'First and Check_Regs(Rs1) <= 1 then
                  if Check_Regs(Rs2) > DataVal'First then
                     Check_Regs(Rd) := Check_Regs(Rs1) * Check_Regs(Rs2);
                     Ret:= Success;
                  else
                     Ret := IllegalProgram;
                  end if;
               else
                  if Check_Regs(Rs1) > 1 and Check_Regs(Rs1) < DataVal'Last then
                     if Check_Regs(Rs2) > DataVal'First/Check_Regs(Rs1) then
                        Check_Regs(Rd) := Check_Regs(Rs1) * Check_Regs(Rs2);
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
      
      end CheckMul;
      
      -- Check if the instruction div is valid
      procedure CheckDiv(Rd : in Reg; 
                         Rs1 : in Reg; 
                         Rs2 : in Reg;
                         Ret : out ReturnCode) is
      begin
         -- should not appear divide by zero
         if Check_Regs(Rs2) /= 0 then
            if Check_Regs(Rs1) > DataVal'First and Check_Regs(Rs1) < DataVal'Last then
               Check_Regs(Rd) := Check_Regs(Rs1) / Check_Regs(Rs2);
               Ret:= Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            Ret:= IllegalProgram;
         end if;
      
      end CheckDiv;
      
      -- Check if the instruction ldr is valid
      procedure CheckLdr(Rd : in Reg; 
                         Rs : in Reg; 
                         Offs : in Offset;
                         Ret : out ReturnCode) is
         A : Addr;
      begin -- The memory address should not out of range
         if Check_Regs(Rs) >= DataVal(-Addr'Last) and Check_Regs(Rs) <= 0 then
            if Offs <= Offset(Addr'Last) and Offs >= - Offset(Check_Regs(Rs)) then
               A := Addr(Check_Regs(Rs) + DataVal(Offs));
               
               -- The memory should be assigned before it is used
               if MemorySigned(A) then
                  Check_Regs(Rd) := Check_Memory(A);
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
               
            else
               Ret := IllegalProgram;
            end if;
         else
            if Check_Regs(Rs) > 0 and Check_Regs(Rs) <= DataVal(Addr'Last) then
               if Offs >= -Offset(Check_Regs(Rs)) and Offs <= Offset(Addr'Last) - Offset(Check_Regs(Rs)) then
                  A := Addr(Check_Regs(Rs) + DataVal(Offs));
                  
                  -- The memory should be assigned before it is used
                  if MemorySigned(A) then
                     Check_Regs(Rd) := Check_Memory(A);
                     Ret := Success;
                  else
                     Ret := IllegalProgram;
                  end if;
                  
               else
                  Ret := IllegalProgram;
               end if;
            else
               if Check_Regs(Rs) > DataVal(Addr'Last) and Check_Regs(Rs) <= DataVal(Addr'Last - Addr'First) then
                  if Offs >= Offset(Addr'First) and Offs <= Offset(Addr'Last) - Offset(Check_Regs(Rs)) then
                     A := Addr(Check_Regs(Rs) + DataVal(Offs));
                     -- The memory should be assigned before it is used
                     if MemorySigned(A) then
                        Check_Regs(Rd) := Check_Memory(A);
                        Ret := Success;
                     else
                        Ret := IllegalProgram;
                     end if;
                  else
                     Ret := IllegalProgram;
                  end if;
               else
                  Ret := IllegalProgram;
               end if;
            
            end if;
         end if;
         
      end CheckLdr;
      
      -- Check if the instruction str is valid
      procedure CheckStr(Ra : in Reg;
                   Offs : in Offset;
                   Rb : in Reg;
                   Ret : out ReturnCode) is
      A : Addr;  
      begin
         if Check_Regs(Ra) >= DataVal(-Addr'Last) and Check_Regs(Ra) <= 0 then
            if Offs <= Offset(Addr'Last) and Offs >= - Offset(Check_Regs(Ra)) then
               A := Addr(Check_Regs(Ra) + DataVal(Offs));
               Check_Memory(A) := Check_Regs(Rb);
               -- mark the address as assigned
               MemorySigned(A) := True;
               Ret := Success;
            else
               Ret := IllegalProgram;
            end if;
         else
            if Check_Regs(Ra) > 0 and Check_Regs(Ra) <= DataVal(Addr'Last) then
               if Offs >= -Offset(Check_Regs(Ra)) and Offs <= Offset(Addr'Last) - Offset(Check_Regs(Ra)) then
                  A := Addr(Check_Regs(Ra) + DataVal(Offs));
                  Check_Memory(A) := Check_Regs(Rb);
                  --mark the address as assigned
                  MemorySigned(A) := True;
                  Ret := Success;
               else
                  Ret := IllegalProgram;
               end if;
            else
               if Check_Regs(Ra) > DataVal(Addr'Last) and Check_Regs(Ra) <= DataVal(Addr'Last - Addr'First) then
                  if Offs >= Offset(Addr'First) and Offs <= Offset(Addr'Last) - Offset(Check_Regs(Ra)) then
                     A := Addr(Check_Regs(Ra) + DataVal(Offs));
                     Check_Memory(A) := Check_Regs(Rb);
                     -- mark the address as assigned
                     Ret := Success;
                  else
                     Ret := IllegalProgram;
                  end if;
               else
                  Ret := IllegalProgram;
               end if;
            
            end if;
         end if;

      end CheckStr;
      
      -- check if the instruction mov is valid
      procedure CheckMov(Rd : in Reg;
                         Offs : in Offset;
                         Ret : out ReturnCode) is
      begin
         Check_Regs(Rd) := DataVal(Offs);
         Ret := Success;
      end CheckMov;
      
   begin
      while (CycleCount < Cycles and Ret = Success) loop
         Inst := Prog(Check_PC);
         DebugPrintInstr(Inst);
         
         case Inst.Op is 
            when ADD =>
               -- if there is a register assigned 0 it should be valid
               if RegsSigned(Inst.AddRs1) or RegsSigned(Inst.AddRs2) then
                  if Check_Regs(Inst.AddRs1) = 0 or Check_Regs(Inst.AddRs2) = 0 then
                     RegsSigned(Inst.AddRd) := True;
                     Check_InCPC(Ret,1);
                  else
                     -- check if the registers used have been assigned value or not
                     if RegsSigned(Inst.AddRs1) and RegsSigned(Inst.AddRs2) then                        
                        CheckAdd(Inst.AddRd,Inst.AddRs1,Inst.AddRs2,Ret);
                        if Ret = Success then
                           -- mark the register as assigned
                           RegsSigned(Inst.AddRd) := True;
                           Check_InCPC(Ret,1);
                        else
                           return True;
                        end if;
                     else
                        return True;
                     end if;
                  end if;
               else
                  return True;
               end if;
                  
            when SUB =>
               if RegsSigned(Inst.SubRs1) or RegsSigned(Inst.SubRs2) then
                  -- if there is a register assigned 0 it should be valid
                  if Check_Regs(Inst.SubRs1) = 0 or Check_Regs(Inst.SubRs2) =0 then
                     RegsSigned(Inst.SubRd) := True;
                     Check_InCPC(Ret,1);
                  else                     
                     -- check if the registers used have been assigned value or not
                     if RegsSigned(Inst.SubRs1) and RegsSigned(Inst.SubRs2) then
                        CheckSub(Inst.SubRd,Inst.SubRs1,Inst.SubRs2,Ret);
                        if Ret = Success then
                           -- mark the register as assigned
                           RegsSigned(Inst.SubRd) := True;
                           Check_InCPC(Ret,1);
                        else
                           return True;
                        end if;
                     else
                        return True;
                     end if;
                  end if;
               else
                  return True;
               end if;
               
               
            when MUL =>
               if RegsSigned(Inst.MulRs1) or RegsSigned(Inst.MulRs2) then
                  -- if there is a register assigned 0 it should be valid
                  if Check_Regs(Inst.MulRs1) = 0 or Check_Regs(Inst.MulRs2) = 0 then
                     RegsSigned(Inst.MulRd) := True;
                     Check_InCPC(Ret,1);
                  else                     
                     -- check if the registers used have been assigned value or not
                     if RegsSigned(Inst.MulRs1) and RegsSigned(Inst.MulRs2) then
                        CheckMul(Inst.MulRd,Inst.MulRs1,Inst.MulRs2,Ret);
                        if Ret = Success then
                           -- mark the register as assigned
                           RegsSigned(Inst.MulRd) := True;
                           Check_InCPC(Ret,1);
                        else
                           return True;
                        end if;
                     else
                        return True;
                     end if;
                  end if;
               else
                  return True;
               end if;
               
               
            when DIV =>
               -- check if the registers used have been assigned value or not
               if RegsSigned(Inst.DivRs1) then
                  if Check_Regs(Inst.DivRs1) = 0 then
                     CheckDiv(Inst.DivRd,Inst.DivRs1,Inst.DivRs2,Ret);
                     if Ret = Success then
                     -- mark the register as assigned
                        RegsSigned(Inst.DivRd) := True;
                        Check_InCPC(Ret,1);
                     else
                        return True;
                     end if;          
                  else
                     if RegsSigned(Inst.DivRs2) then
                        CheckDiv(Inst.DivRd,Inst.DivRs1,Inst.DivRs2,Ret);
                        if Ret = Success then
                           -- mark the register as assigned
                           RegsSigned(Inst.DivRd) := True;
                           Check_InCPC(Ret,1);
                        else
                           return True;
                        end if;
                     else
                        return True;
                     end if;
                  end if;                  
               else
                  return True;
               end if;               
                     
               
            when JMP =>
               Check_InCPC(Ret,Inst.JmpOffs);
               if Ret = IllegalProgram then
                  return True;
               end if;
               
            when JZ =>
               -- check if the register used have been assigned value or not
               if RegsSigned(Inst.JzRa) then
                  if Check_Regs(Inst.JzRa) = 0 then
                     Check_InCPC(Ret,Inst.JzOffs);
                  else
                     Check_InCPC(Ret,1);
                  end if;
               else
                  return True;
               end if;
               
            when NOP =>
               Check_InCPC(Ret,1);
               
            when Instruction.RET =>
               return False;
               
            when MOV =>
               CheckMov(Inst.MovRd,Inst.MovOffs,Ret);
               if Ret = Success then
                  -- mark the register as assigned
                  RegsSigned(Inst.MovRd) := True;
                  Check_InCPC(Ret,1);
               else
                  return True;
               end if;
               
            when LDR =>
               -- check if the register used have been assigned value or not
               if RegsSigned(Inst.LdrRs) then
                  CheckLdr(Inst.LdrRd,Inst.LdrRs,Inst.LdrOffs,Ret);
                  if Ret = Success then
                     -- mark the register as assigned
                     RegsSigned(Inst.LdrRd) := True;
                     Check_InCPC(Ret,1);
                  else
                     return True;
                  end if;
               else
                  return True;
               end if;   
               
            when STR =>
               -- check if the register used have been assigned value or not
               if RegsSigned(Inst.StrRa) and RegsSigned(Inst.StrRb) then
                  CheckStr(Inst.StrRa,Inst.StrOffs,Inst.StrRb,Ret);
                  if Ret = Success then
                     Check_InCPC(Ret,1);
                  else
                     return True;
                  end if;
               else
                  return True;
               end if;
               
         end case;
         
         CycleCount := CycleCount + 1;   
      end loop;
      
      -- The program has no RET
      if Ret = Success then
         return True;
      else
         return True;
      end if;
      
   end DetectInvalidBehaviour;
      

end Machine;
