//Addresses and data
sig Addr {}
sig Data {}

//A cache system consists of main memory and cached memory, but mapping addresses to data
sig CacheSystem {
	main, cache: Addr -> lone Data
}

//Initially there is no memory allocated
pred init [c: CacheSystem] {
	no c.main + c.cache
}

//Write data to a specified address in the cache
pred write [c, c': CacheSystem, a: Addr, d: Data] {
	c'.main = c.main
	c'.cache = c.cache ++ a -> d
}

//Read data from a specified address in the cache
pred read [c: CacheSystem, a: Addr, d: Data] {
	some d
	d = c.cache [a]
}

//Load some data from the main memory in the cache
//Note that this is non-deterministic: it does not specific what to load. This is left to the implementation
pred load [c, c': CacheSystem] {
	some addrs: set c.main.Data - c.cache.Data |
		c'.cache = c.cache ++ addrs <: c.main
	c'.main = c.main
}

//Flush memory from the cache back into the main memory.
//Note this is also non-deterministic
pred flush [c, c': CacheSystem] {
	some addrs: some c.cache.Data {
		c'.main = c.main ++ addrs <: c.cache
		c'.cache = c.cache - addrs -> Data
	}
}

//If a load is performed between a write and a read, this should not be observable.
//That is, if we perform the sequence: read, write, load, and read, 
//then reading the same address in both reads should return the same value,
//unless the write in between overwrote that value (i.e. a1=a2)
assert LoadNotObservable {
	all c, c', c": CacheSystem, a1, a2: Addr, d1, d2, d3: Data |
		{
		read [c, a2, d2]
		write [c, c', a1, d1]
		load [c', c"]
		read [c", a2, d3]
		} implies d3 = (a1=a2 => d1 else d2)
	}

check LoadNotObservable for 5

