package body Task5 with
SPARK_Mode => On 
is
   
   procedure Task5Procedure(A : in Boolean; B : in Boolean; C : out Boolean) is
   begin
      if not A then
	 C := True;
      else
	 if A then
	    if B then
	       C := True;
	    else
		 C := False;
	    end if;
	 else
	    C := False;
	 end if;
      end if;
	    
   end Task5Procedure;
end Task5;

