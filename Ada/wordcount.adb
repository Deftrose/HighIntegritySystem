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

begin

   loop

      Get(Ch); -- Get a character from standard input
      if Ch /= '#' then
         NumChars := NumChars +1;
         Word := Word & Ch;
         Put("Got a new character " & ": " & Ch);
         Put(" number of chars :"); Put(NumChars);
         Ada.Text_IO.New_Line;
      else
         Put("The word is :" & ASU.To_String(Word));
         break;
      end if;

   end loop;
      
end WordCount;
