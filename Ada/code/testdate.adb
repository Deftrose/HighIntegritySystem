with Ada.Text_IO; use Ada.Text_IO;
with Date;

procedure TestDate is
   Date1, Date2 : Date.DateType;
begin
   -- Increment a long month
   Date.Create(Date1, 31, 1, 2013);
   Date.Increment(Date1);
   Date.Create(Date2, 1, 2, 2013);
   if not Date.Equals(Date1, Date2) then
      Put_Line("Test failed on date "); Date.Print(Date1);
   end if;
   
   -- Increment a short month
   Date.Create(Date1, 30, 4, 2013);
   Date.Increment(Date1);
   Date.Create(Date2, 1, 5, 2013);
   if not Date.Equals(Date1, Date2) then
      Put_Line("Test failed on date "); Date.Print(Date1);
   end if;
   
   -- Increment last day of Feb on a non-leap year
   Date.Create(Date1, 28, 2, 2013);
   Date.Increment(Date1);
   Date.Create(Date2, 1, 3, 2013);
   if not Date.Equals(Date1, Date2) then
      Put_Line("Test failed on date "); Date.Print(Date1);
   end if;
   
   -- Increment 28 Feb on a leap year
   Date.Create(Date1, 28, 2, 2012);
   Date.Increment(Date1);
   Date.Create(Date2, 29, 2, 2012);
   if not Date.Equals(Date1, Date2) then
      Put_Line("Test failed on date "); Date.Print(Date1);
   end if;
     
   -- Increment 29 Feb on a leap year
   Date.Increment(Date1);
   Date.Create(Date2, 1, 3, 2012);
   if not Date.Equals(Date1, Date2) then
      Put_Line("Test failed on date "); Date.Print(Date1);
   end if;
   
   -- Increment date on final day of year
   Date.Create(Date1, 31, 12, 2013);
   Date.Increment(Date1);
   Date.Create(Date2, 1, 1, 2014);
   if not Date.Equals(Date1, Date2) then
      Put_Line("Test failed on date "); Date.Print(Date1);
   end if;
   
   -- Increment a day not on the end of the month
   Date.Create(Date1, 30, 1, 2013);
   Date.Increment(Date1);
   Date.Create(Date2, 31, 1, 2013);
   if not Date.Equals(Date1, Date2) then
      Put_Line("Test failed on date "); Date.Print(Date1);
   end if;
   
end TestDate;
