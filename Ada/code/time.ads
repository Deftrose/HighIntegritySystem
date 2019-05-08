with Date;

package Time is

   subtype MinuteType is Integer range    0 .. 59;
   subtype HourType is Integer range    0 .. 23;
   
   -- A type for dates
   type TimeType is private;

   -- Create a new date from a specified day, month, and year
   procedure Create(Time : out TimeType; 
		    Hour : in HourType;
		    Minute : in MinuteType;
		    TDate : in Date.DateType);
   
   -- Increment the time
   procedure Increment(Time : in out TimeType);
   
   -- Getter functions
   function GetMinute(Time : in TimeType) return HourType;
   function GetHour(Time : in TimeType) return HourType;
   function GetDate(Time : in TimeType) return Date.DateType;
   
   -- Returns true if and only if the two times are equivalent
   function Equals(Time1, Time2 : in TimeType) return Boolean;
   
   -- Print to stdout
   procedure Print(Time : in TimeType);
private
   -- A record type for time. The format of the record is hidden from
   --  packages using this package
   type TimeType is
      record
	 Hour : HourType;
	 Minute : MinuteType;
	 TDate : Date.DateType;
      end record; 
end Time;
