--  Generic Stack Specification 
--  ===========================
--
--  This is a generic stack package. There are two parameters to the
--  stack package: the size of the stack and the type of the data
--  items in the stack.
--
generic
   Max_Size: Positive;          -- The maximum size of the stack.
   type Item is private;        -- The type of items in the stack. The type must
                                -- be definite, and the private means that this
                                -- package may not examine its internals.
package ProtectedStack is
   
   type StackType is private;

   -- Exceptions.
   Stack_Underflow, Stack_Overflow: exception;
   
   -- The public interface to the stack consists of the following
   --  operations. The stack is "protected" which means that the tasks
   --  have muitually exclusive access to the stack operations. They
   --  are declared just like the "entry" points in a task type
   --  declaration and are implemented using "entry" keywords as
   --  well. Entry calls are the main means of communication between
   --  concurrent tasks in Ada so this is effectively an Abstract Data
   --  Type that protects the Stack by enforcing mutually exlcusive
   --  access.
   
   protected type Stack is
      entry Push(I: in Item); 
      entry Pop(I: out Item);
      entry Top(I: out Item); 
      entry Empty(EmptyStack: out Boolean); 
      entry Full(FullStack: out Boolean);
      entry Clean; 
   private 
      Stk : StackType;
   end Stack;
   
private
   
   type StackData is array(1.. Max_Size) of Item;
   type StackType is record
      Size: Integer range 0 .. Max_Size := 0;
      Data: StackData;
   end record;
      
end ProtectedStack;
