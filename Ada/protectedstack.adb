--  Protected Stack Specification 
--  ===========================
--
-- The implementation uses the private variable "Stk"declared in the
--  private parts of the protected stack specification (see
--  ProtectedStack.ads).
--
-- Another feature of the Protected Stack implementation is the use of
--  "when" clauses in the implementation of each entry procedure that
--  acts as a guard to the entry call. Gnat (at least) enforces "when"
--  clauses and since we want any task to *Rendezvous" with any
--  protected stack entry procedure when possible the guards are
--  simply True for our implementation. We could have written 
--
--          when Stk.Size < Max_Size
--
--  but Ada also requires that every possibility is covered by guards
--  to entry calls.
package body ProtectedStack is
   
   protected body Stack is 
      
      entry Push(I: in Item)
      when True is
      begin
	 if Stk.Size < Max_Size then
	    Stk.Size := Stk.Size + 1;
	    Stk.Data(Stk.Size) := I;
	 else
	    raise Stack_Overflow;
	 end if;
      end Push;

      entry Pop(I: out Item) 
      when True is
      begin
	 if Stk.Size > 0 then
	    I := Stk.Data(Stk.Size);
	    Stk.Size := Stk.Size - 1;
	 else
	    raise Stack_Underflow;
	 end if;
      end Pop;

      entry Top(I: out Item)
      when True is
      begin
	 if Stk.Size > 0 then
	    I := Stk.Data(Stk.Size);
	 else
	    raise Stack_Underflow;
	 end if;
      end Top;

      entry Empty(EmptyStack: out Boolean) 
      when True is
      begin
	 EmptyStack := (Stk.Size = 0);
      end Empty;

      entry Full(FullStack: out Boolean) 
      when True is
      begin
	 FullStack := (Stk.Size = Max_Size);
      end Full;

      entry Clean
      when True is
      begin
	 Stk.Size := 0;
      end Clean;
      
   end Stack;
   
end ProtectedStack;
