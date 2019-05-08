with Ada.Text_IO; use Ada.Text_IO;

package body Date is
   
   -- List of months with 31 days
   type MonthRange is new Integer range 1..7;
   LongMonths : array(MonthRange) of MonthType := (1,3,5,7,8,10,12);
   
   -- A private function. Returns true if and only if year is a leap year.
   function IsLeapYear(Year : in YearType) return Boolean is
   begin
      if Year mod 400 = 0 then
	 return True;
      elsif Year mod 100 = 0 then
	 return False;
      elsif Year mod 4 = 0 then
	 return True;
      end if;
      return False;
   end IsLeapYear;
   
   -- Private. Returns true if and only if the element is in the
   --  array "LongMonths".
   function IsLongMonth(Month : in MonthType) return Boolean is
   begin
      for I in MonthRange'Range loop
	 if Month = LongMonths(I) then
	    return True;
	 end if;
      end loop;
      return False;
   end IsLongMonth;
   
   -- Create a new date from a specified day, month, and year
   procedure Create(Date : out DateType; 
		    Day : in DayType;
		    Month : in MonthType;
		    Year : in YearType) is
   begin
      Date.Day := Day;
      Date.Month := Month;
      Date.Year := Year;
   end Create;
   
   -- Increment the date
   procedure Increment(Date : in out DateType) is
   begin
      -- Increment from Feb to Mar if day is 29 and a leap year, or
      --  day is 28 and a non-leap year
      if Date.Month = 2 then
	 if (Date.Day = 29 and IsLeapYear(Date.Year)) or
	   (Date.Day = 28 and not IsLeapYear(Date.Year)) then
	    Date.Month := 3;
	    Date.Day := 1;
	 else
	    Date.Day := Date.Day + 1;
	 end if;
	 -- Increment month if day is 31 and month is long
      elsif Date.Day = 31 and IsLongMonth(Date.Month) then
	 if (Date.Month = 12) then
	    Date.Month := 1;
	    Date.Year := Date.Year + 1;
	 else
	    Date.Month := Date.Month + 1;
	 end if;
	 Date.Day := 1;
	 -- Increment month if day is 30 and month is not long
      elsif Date.Day = 30 and not IsLongMonth(Date.Month) then
	 Date.Month := Date.Month + 1;
	 Date.Day := 1;
      else
	 Date.Day := Date.Day + 1;
      end if;
   end Increment;
   
   -- Getter functions
   function GetDay(Date : in DateType) return DayType is
   begin
      return Date.Day;
   end GetDay;
   
   function GetMonth(Date : in DateType) return MonthType is
   begin
      return Date.Month;
   end GetMonth;
   
   function GetYear(Date : in DateType) return YearType is
   begin
      return Date.Year;
   end GetYear;   
   
   function Equals(Date1, Date2 : in DateType) return Boolean is
   begin
      if Date1.Day = Date2.Day and
	Date1.Month = Date2.Month and
	Date1.Year = Date2.Year then
	 return True;
      else
	 return False;
      end if;
   end Equals;
   
   procedure Print(Date : in DateType) is
   begin
      Put(Integer'Image(GetDay(Date)) & " -" &
	    Integer'Image(GetMonth(Date)) & " -" &
	    Integer'Image(GetYear(Date)));
   end Print;
end Date;
