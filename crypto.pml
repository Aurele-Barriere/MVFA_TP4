mtype = { K_Alice, K_Bob, K_Charlie, None }

typedef msg{
	int data;
	mtype key1;
	mtype key2
	}

msg secret;
byte bob_read = 0;
byte charlie_read = 0;

ltl secret_safety { [] (!charlie_read) };
ltl protocol_ok { <> bob_read };

proctype Alice(int data) {
do
:: atomic{ (secret.key1 == K_Alice && secret.key2 != None) -> secret.key1 = None }
:: atomic{ (secret.key2 == K_Alice && secret.key1 != None) -> secret.key2 = None }
od
}

proctype Bob() {
do
:: atomic{ (secret.key1 == None  && secret.key2 != None ) -> secret.key1 = K_Bob }
:: atomic{ (secret.key2 == None  && secret.key1 != None ) -> secret.key2 = K_Bob }

:: atomic{ (secret.key1 == K_Bob && secret.key2 == K_Bob) -> bob_read = 1; break }
:: atomic{ (secret.key1 == None  && secret.key2 == None ) -> bob_read = 1; break }
:: atomic{ (secret.key1 == K_Bob && secret.key2 == None ) -> bob_read = 1; break }
:: atomic{ (secret.key2 == K_Bob && secret.key1 == None ) -> bob_read = 1; break }
od
}

proctype Charlie() {
msg memory;
memory.data = secret.data;
memory.key1 = secret.key1;
memory.key2 = secret.key2;


do
:: atomic{
     memory.data = secret.data;
     memory.key1 = secret.key1;
     memory.key2 = secret.key2;
   }
:: atomic{
     secret.data = memory.data;
     secret.key1 = memory.key1;
     secret.key2 = memory.key2;
   }
:: atomic{ (memory.key1 == None) -> memory.key1 = K_Charlie }
:: atomic{ (memory.key2 == None) -> memory.key2 = K_Charlie }

:: atomic{ (secret.key2 == None      && secret.key1 == None) -> charlie_read = 1; break }
:: atomic{ (secret.key1 == K_Charlie && secret.key2 == None) -> charlie_read = 1; break }
:: atomic{ (secret.key2 == K_Charlie && secret.key1 == None) -> charlie_read = 1; break }
od
}

init {
     secret.data = 867864;
     secret.key1 = K_Alice;
     secret.key2 = None;     		
     run Alice();
     run Bob();
     run Charlie(); 
}


/*
Without running Charlie, the ltl property [protocol_ok] and [secret_safety] are checked.

*/