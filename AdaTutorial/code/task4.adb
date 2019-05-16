package body Task4 with
SPARK_Mode => On
is

   procedure Task4Procedure(AnArray : in out MyArray; AnIndex : in Index) is
   begin
      if AnArray(AnIndex) <= Integer'Last - 1 then
         if AnIndex <= Index'Last - 1 then
            AnArray(AnIndex) := AnArray(AnIndex + 1);
            end if;
      end if;
   end Task4Procedure;
end Task4;

