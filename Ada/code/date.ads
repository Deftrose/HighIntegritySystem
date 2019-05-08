package Date is

   subtype DayType   is Integer range    1 .. 31;
   subtype MonthType is Integer range    1 .. 12;
   subtype YearType  is Integer range 1800 .. 2100;
   
   -- A type for dates
   type DateType is private;

   -- Create a new date from a specified day, month, and year
   procedure Create(Date : out DateType; 
		    Day : in DayType;
		    Month : in MonthType;
		    Year : in YearType);
   
   -- Increment the date
   procedure Increment(Date : in out DateType);
   
   -- Getter functions
   function GetDay(Date : in DateType) return DayType;
   function GetMonth(Date : in DateType) return MonthType;
   function GetYear(Date : in DateType) return YearType;
   
   -- Returns true if and only Date1 and Date2 represent the same date
   function Equals(Date1, Date2 : in DateType) return Boolean;
   
   -- Print to stdout
   procedure Print(Date : in DateType);
private
   -- A record type for dates. The format of the record is hidden from
   --  packages using this package
   type DateType is
      record
	 Day   : DayType;
	 Month : MonthType;
	 Year  : YearType;
      end record; 
end Date;
