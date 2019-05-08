with Ada.Text_IO; use Ada.Text_IO;
with Date;

package body Time is
   procedure Create(Time : out TimeType; 
		    Hour : in HourType;
		    Minute : in MinuteType;
		    TDate : in Date.DateType) is
   begin
      Time.Minute := Minute;
      Time.Hour := Hour;
      Time.TDate := TDate;
   end Create;
   
   procedure Increment(Time : in out TimeType) is
   begin
      if Time.Minute = 59 then
	 Time.Minute := 0;
	 if Time.Hour = 23 then
	    Time.Hour := 0; Date.Increment(Time.TDate);
	 else
	    Time.Hour := Time.Hour + 1;
	 end if;
      else
	 Time.Minute := Time.Minute + 1;
      end if;
   end Increment;
   
   -- Getter functions
   function GetMinute(Time : in TimeType) return HourType is
   begin
      return Time.Minute;
   end GetMinute;
    
   function GetHour(Time : in TimeType) return HourType is
   begin
      return Time.Hour;
   end GetHour;

   function GetDate(Time : in TimeType) return Date.DateType is
   begin
      return Time.TDate;
   end GetDate;
   
   function Equals(Time1, Time2 : in TimeType) return Boolean is
   begin
      if Time1.Minute = Time2.Minute and
	Time1.Hour = Time2.Hour and
	Date.Equals(Time1.TDate, Time2.TDate) then
	 return True;
      else
	 return False;
      end if;
   end Equals;
   
   procedure Print(Time : in TimeType) is
   begin
      Put(Integer'Image(GetMinute(Time)) & ":" &
	    Integer'Image(GetHour(Time)) & "; ");
      Date.Print(GetDate(Time));
   end Print;
end Time;
