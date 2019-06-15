with Ada.Text_IO; 
use  Ada.Text_IO;

with Ada.Integer_Text_IO;
use  Ada.Integer_Text_IO;

with ProtectedStack;
with Ada.Strings.Unbounded;

with Ada.Characters.Latin_1;

-- The WordCount program counts the number of characters and words in
--  a string received from standard input. A word is any alphanum
--  character separated by a space or tab
procedure WordCount is
   
   package ASU renames Ada.Strings.Unbounded;
   use ASU;   
   package StringStack is new ProtectedStack(100, ASU.Unbounded_String);
   
   Ch        : Character;            -- the current character
   Word      : ASU.Unbounded_String; -- the current word
   
   -- The number of characters and words
   NumChars : Integer := 0;
   NumWords : Integer := 0;
   
   -- a stack for putting words into
   St : StringStack.Stack;
   
   -- for testing is the stack is empty
   IsEmpty : Boolean;
   
begin
   
   Get(Ch);
   
   Word := ASU.To_Unbounded_String("");
   
   while (Ch /= '#') loop
      
      NumChars := NumChars + 1;
      
      -- if a space or tab, we encounter a new word
      if Ch = ' ' or Ch = Ada.Characters.Latin_1.HT then	 
	 
	 -- consume remaining spaces and tabs
	 while Ch = ' ' or Ch = Ada.Characters.Latin_1.HT loop
	    Get(Ch);
	 end loop;
	 
	 NumWords := NumWords + 1;
	 St.Push(Word);
	 Word := ASU.To_Unbounded_String("");
	 
      else
	 Word := Word & Ch;
	 Get(Ch);
      end if;
      
   end loop;
   
   -- push the terminating word
   NumWords := NumWords + 1;
   St.Push(Word);

   Put(NumWords); New_Line;
   Put(NumChars); New_Line;
   
   -- print the words on the stack
   St.Empty(IsEmpty);
   while not IsEmpty loop
      St.Pop(Word);
      Put(ASU.To_String(Word) & " ");
      St.Empty(IsEmpty);
   end loop;
end WordCount;
