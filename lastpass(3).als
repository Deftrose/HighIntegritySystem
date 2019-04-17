module LastPass

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
 */

sig URL {}
sig Username {}
sig Password {}
sig PassBook {password : Username -> URL -> Password}

//Add an axiom stating that all PassBooks have no duplicates
// This is equivalent to instead putting "lone Password" instead of "Password" 
//  in PassBook's definition
fact noDuplicates {
    all pb : PassBook, user : Username, url : URL | lone pb.password[user][url]
}

//Add a password for a new user/url pair
pred add [pb, pb': PassBook, url : URL, user: Username, pwd: Password] {
    no pb.password[user][url]
    pb'.password = pb.password + (user->url->pwd)
}

//Delete an existing password
pred delete [pb, pb': PassBook, url : URL, user: Username] {
    one pb.password[user][url]
    pb'.password = pb.password - (user->url->Password)
}

//Update an existing password
pred update [pb, pb': PassBook, url : URL, user: Username, pwd: Password] {
    pb'.password = pb.password ++ (user->url->pwd)
}

//Return the password for a given user/URL pair
fun lookup [pb: PassBook, url : URL, user : Username] : lone Password {
    pb.password[user][url]
}

//Check if a user's passwords for two urls are the same
pred samePassword [pb : PassBook, url1, url2 : URL, user : Username] {
    lookup [pb, url1, user] = lookup [pb, url2, user]
}

//Retrieve all of the passwords and the url they are for, for a given user
pred retrieveAll [pb: PassBook, user : Username, pwds : URL -> Password] {
    pwds = (pb.password)[user]
}

//Initialise the PassBook to be empty
pred init [pb: PassBook] {
    no pb.password
}

// run the add operation
run add for 2
run add for 5 URL, 5 Username, 10 Password, 2 PassBook

run update for 2

//If we add a new password, then we get this password when we look it up
assert addWorks {
    all pb, pb': PassBook, url : URL, user : Username, p : Password |
        add [pb, pb', url, user, p] => (lookup [pb', url, user] = p)
}

//If we update an existing password, then we get this password when we look it up
assert updateWorks {
    all pb, pb': PassBook, url : URL, user : Username, p' : Password |
            update [pb, pb', url, user, p'] => (lookup [pb', url, user] = p')
}

//If we add and then delete a password, we are back to 'the start'
assert deleteIsUndo {
    all pb1, pb2, pb3: PassBook, url : URL, user : Username, pwd : Password |
        add [pb1, pb2, url, user, pwd] && delete [pb2, pb3, url, user]
            => pb1.password = pb3.password
}

//lookup only ever returns at most one result
assert lookupLOne {
  all pb : PassBook, url : URL, user : Username |
      lone lookup[pb, url, user]
}

check addWorks for 5 but 2 PassBook expect 0
check updateWorks for 5 but 2 PassBook expect 0
check deleteIsUndo for 2 expect 0
check lookupLOne for 2 but 1 PassBook expect 0
