package body Task3 with
     SPARK_Mode => On
is

   procedure Task3Procedure(Input : in Integer; Result : out Integer)
   is
   begin
      if Input * 10 <= Integer'Last and
        Input * 10 >= Integer'First then
         Result := Input * 10;
      else
         Result := Input;
      end if;
   end Task3Procedure;
end Task3;

