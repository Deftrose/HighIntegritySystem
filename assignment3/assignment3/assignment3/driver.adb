with Instruction;
use Instruction;
with Machine;
use Machine;
with Debug; use Debug;

procedure Driver with SPARK_Mode is
   Prog : Program := (others => (Op => NOP));
   Code : ReturnCode;
   Result : Integer;
   HasInvalidBehaviour : Boolean;
   
   test2 : Program := (1 => (OP => MOV, MovRd => 1, MovOffs => 0), 2=> (OP => JZ, JzRa => 1, JzOffs => -100), 
                      3 => (OP => RET, RetRs => 1), others => (OP => NOP));
   JMPtest : Program := (1 => (OP => MOV, MovRd => 1, MovOffs => 1), 2=> (OP => MOV, MovRd => 2, MovOffs => 1),
                         3 => (OP => JMP, JmpOffs => -100), others => (OP => RET, RetRs => 1));
   test : Program := (1 => (OP => MOV, MovRd => 1, MovOffs => 1), 2=> (OP => MOV, MovRd => 2, MovOffs => 1), 
                      3 => (OP => STR, StrRa => 1, StrOffs => 1, StrRb => 2),
                      4 => (OP => LDR, LdrRd => 1, LdrRs => 2, LdrOffs => 1),
                        5 => (OP => RET, RetRs => 2),others =>(Op => NOP)  );
begin
   -- initialise the random number generators used to generate
   -- random instructions. Commenting this out may yield predictable
   -- (i.e. non-random) output
   Instruction.Init;
      
   -- generate a random program
   Put_Line("Generating Random Program...");
   for I in Prog'Range loop
      GenerateRandomInstr(Prog(I));
   end loop;
   
   Put_Line("Analysing Program for Invalid Behaviour...");
   HasInvalidBehaviour := DetectInvalidBehaviour(test,MAX_PROGRAM_LENGTH);
   Put("Analysis Result: ");
   Put(HasInvalidBehaviour'Image); New_Line;

   
   -- run the program
   Put_Line("Executing program...");
   ExecuteProgram(test,MAX_PROGRAM_LENGTH,Code,Result);
   Put("Return Code: ");
   Put(Code'Image);
   if Code = Success then
      Put(" Result: "); Put(Result);
   end if;
   New_Line;   

end Driver;
