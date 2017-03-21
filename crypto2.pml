mtype = { K_Alice, K_Bob, K_Charlie, None };

typedef msg {
	int data;
	mtype key1;
	mtype key2
};

ltl protocol_ok { [] (<> bob_read) }

chan alice_to_charlie = [0] of { msg };
chan charlie_to_bob = [0] of { msg };
byte bob_read = 0;
byte charlie_read = 0;

proctype Alice(int secret_data) {
  msg message;
  do
  /* The channel is empty, Alice sends her message */
  :: atomic {
    empty(alice_to_charlie)
		-> message.data = secret_data; message.key1 = K_Alice; message.key2 = None
    -> bob_read = 0
		-> alice_to_charlie!message
  }

  :: atomic {
    alice_to_charlie?message;

		if
		/* Alice removes her own key if there's another key */
		:: (message.key1 == K_Alice && message.key2 != None)
			-> message.key1 = None;
		:: (message.key2 == K_Alice && message.key1 != None)
	    -> message.key2 = None;
		fi;

		/* Alice can then send the message */
		alice_to_charlie!message
  }
  od
}

proctype Charlie() {
	msg message;
	do
	:: atomic {
		/* case one: read from alice */
		alice_to_charlie?message;

		/* sends the message to bob */
		charlie_to_bob!message;
	};

	:: atomic {
		/* case two: reads from bob */
		charlie_to_bob?message;

		/* sends the message to alice */
		alice_to_charlie!message
	};
	od
}

proctype Bob() {
  msg message;
  do
	:: atomic {
		/* first read the message */
		charlie_to_bob?message;
		if

		/* There is only one key but not his, Bob add its own*/
	  :: (message.key1 != None && message.key1 != K_Bob && message.key2 == None)
	    -> message.key2 = K_Bob -> charlie_to_bob!message;
	  :: (message.key2 != None && message.key2 != K_Bob && message.key1 == None)
	    -> message.key1 = K_Bob -> charlie_to_bob!message;

		/* There is only Bob's key: Bob reads the message, but doesn't send any */
		:: (message.key1 == K_Bob && message.key2 == None) || (message.key2 == K_Bob && message.key1 == None)
			-> bob_read = 1;

		/* default case: Bob just re-emits the message unchanged */
		:: else -> charlie_to_bob!message;
		fi
	}
  od
}

init {
	atomic {
		run Alice(867864);
		run Charlie();
		run Bob()
	}
}
