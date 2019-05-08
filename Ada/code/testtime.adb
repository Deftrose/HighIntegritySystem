with Ada.Text_IO; use Ada.Text_IO;
with Time;
with Date;

procedure TestTime is
   Time1, Time2 : Time.TimeType;
   Date1, Date2 : Date.DateType;
begin
   -- Increment at the end of an hour
   Date.Create(Date1, 15, 1, 2013);
   Time.Create(Time1, 1, 59, Date1);
   Time.Increment(Time1);
   Time.Create(Time2, 2, 0, Date1);
   if not Time.Equals(Time1, Time2) then
      Put("Test 1 failed on time "); Time.Print(Time1);
   end if;
   
   -- Increment at the end of a day
   Time.Create(Time1, 23, 59, Date1);
   Time.Increment(Time1);
   Date.Create(Date2, 16, 1, 2013);
   Time.Create(Time2, 0, 0, Date2);
   if not Time.Equals(Time1, Time2) then
      Put("Test 2 failed on time "); Time.Print(Time1);
   end if;
   
   -- Increment in the middle of an hour and minute
   Time.Create(Time1, 12, 30, Date1);
   Time.Increment(Time1);
   Time.Create(Time2, 12, 31, Date1);
   if not Time.Equals(Time1, Time2) then
      Put("Test 3 failed on time "); Time.Print(Time1);
   end if;
end TestTime;
