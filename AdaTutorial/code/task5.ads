package Task5 with
SPARK_Mode => On
is

   -- C is true if and only if A implies B.
   procedure Task5Procedure(A : in Boolean; B : in Boolean; C : out Boolean)
   with
      Depends => (C => (A, B));

end Task5;

