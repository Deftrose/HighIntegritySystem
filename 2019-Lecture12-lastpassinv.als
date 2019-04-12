module LastPassInv

/*
 * LastPass password map
 *
 * A simple example to explain basics of Alloy. 
 *
 * The 'PassBook' keeps track of a set of users' passwords for a set of URLs. 
 * For each User/URL pair, there is at most one password. 
 * Passwords can be added, deleted, looked up, and changed. 
 * A user can also request all of their password for all URLs.
 *
 * author: Tim Miller
 *
 * Changes:
 * Toby Murray (March 2017) 
       - Switch to simpler representation
       - Fix definition of updateWorks predicate
       - Make noDuplicates an invariant, not an axiom
 */

sig URL {}
sig Username {}
sig Password {}
sig PassBook {password : Username -> URL -> Password}

// the type of results, of which there are only two: ResultOK and ResultError
abstract sig Result {}
one sig ResultOK, ResultError extends Result {}

//Add an predicate saying that there is at most one
// password for each username, URL pair
pred noDuplicates [pb : PassBook] {
  all user : Username, url : URL | lone pb.password[user][url]
}

//Define an invariant which is just that there are no duplicates
pred Inv [pb : PassBook] {
  noDuplicates[pb]
}

// add's precondition for its normal behaviour
pred addPre[pb : PassBook, url : URL, user  : Username, pwd : Password] {
    no pb.password[user][url]
}

//Add a password for a new user/url pair
pred addNormal [pb, pb': PassBook, url : URL, user: Username, pwd: Password, res : Result] {
    addPre[pb, url, user, pwd]
    pb'.password = pb.password + (user->url->pwd)
    res in ResultOK
}

//Behaviour of add in exceptional case
pred addExceptional [pb, pb': PassBook, url : URL, user: Username, pwd: Password, res : Result] {
    not addPre[pb, url, user, pwd]
    pb' = pb
    res in ResultError
}

//Add's behaviour overall: it includes both the normal and exceptional cases
pred add [pb, pb': PassBook, url : URL, user: Username, pwd: Password, res : Result] {
  addNormal [pb, pb', url, user, pwd, res] or 
  addExceptional [pb, pb', url, user, pwd, res]
}

//Delete's precondition for its normal behaviour
pred deletePre[pb : PassBook, url : URL, user : Username] {
  one pb.password[user][url]
}


//Delete an existing password
pred deleteNormal [pb, pb': PassBook, url : URL, user: Username, res : Result] {
  deletePre[pb, url, user]
  pb'.password = pb.password - (user->url->Password)
  res in ResultOK
}

//Delete's behaviour in the exceptional case
pred deleteExceptional [pb, pb': PassBook, url : URL, user: Username, res : Result] {
  not deletePre[pb, url, user]
  pb'= pb
  res in ResultError
}


//Delete's behaviour overall: it includes both the normal and exceptional cases
pred delete [pb, pb': PassBook, url : URL, user: Username, res : Result] {
  deleteNormal [pb, pb', url, user, res] or 
  deleteExceptional [pb, pb', url, user, res]
}

//Initialise the PassBook to be empty
pred init [pb: PassBook] {
    no pb.password
}

// run the add operation
run add for 2 but 1 PassBook
run add for 5 URL, 5 Username, 10 Password, 2 PassBook


//the invariant is true for the initial state
assert initInv {
  all pb : PassBook | init[pb] => Inv[pb]
}

//the add operation preserves the invariant: if the invariant held before add, 
// it will continue to hold afterwards
assert addInv {
  all pb,pb' : PassBook, user : Username, url : URL, pwd : Password, res : Result | 
    Inv[pb] and add[pb,pb',url,user,pwd,res] => Inv[pb']
}

//the delete operation preserves the invariant
assert deleteInv {
  all pb,pb' : PassBook, user : Username, url : URL, res : Result |
    Inv[pb] and delete[pb,pb',url,user,res] => Inv[pb']
}


check initInv for 5 expect 0
check addInv for 2 expect 0
check deleteInv for 5 expect 0
