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

pred destroy [c, c' : CacheSystem, a : Addr] {
	c'.main = c.main - (a -> Data)
	c'.cache = c.cache - (a -> Data)
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

assert LoadPreserves {
	all c, c' : CacheSystem | load [c, c'] implies c'.main in c.main
}

check LoadPreserves for 5

assert CannotReadInitially {
	all c : CacheSystem, a : Addr, d : Data | init[c] => not read[c, a, d] 
}

check CannotReadInitially for 5

/* 
 * This check fails because, while the load and flush operations move memory between main 
 * and the cache, and there is never any address in both at the same time, the OnlyOne assert
 * is checking only the 'destroy' operation, which takes any main memory and cache operation.
 *  That is, the Alloy Analyser does not consider how the values for c and c' come about: it just
 * checks them. For this property to be preserved, we would need to add an invariant to the model
 * that specifies that no address is in both main and cache, and then check that this invariant holds
 * for all operations. Then, we could modify below to state: destroy[c, c', a] and inv[c] => ...
 */
assert OnlyOneMemoryDestroyed {
	all c, c' : CacheSystem, a : Addr | destroy [c, c', a] => (c'.main = c.main or c'.cache = c.cache)
}
check OnlyOneMemoryDestroyed for 5
