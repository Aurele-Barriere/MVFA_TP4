mtype = { K_Alice, K_Bob, K_Charlie, None };

typedef msg {
	int data;
	mtype key1;
	mtype key2
};

ltl protocol_ok { [] (<> bob_read) }
ltl attack { [] (!charlie_read) }

/* We use two channels. Indeed, if we use only one, the flow of the program becomes much harder to control.

Furthermore, with only one channel, the attacker could simply intercept one message, and send it back with it's own key instead of Bob's. The choice we made does not model a real life situation: if Alice can't distinguish Charlie's key from Bob's, this is a perfectly valid attack.

This highlight the fact that this protocol doesn't work only because the agents can't verify that a message has been encrypted by the right agent. Public-key cryptography provides a way to prevent this kind of attacks. */
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

proctype Charlie(byte attacker) {
	msg message;
	msg attack_message;
	do
	:: atomic {
		/* case one: read from alice */
		alice_to_charlie?message;

		if
		/* keep the message if there's only one key, and add its own key */
		:: (message.key1 != None && message.key2 == None)
			-> attack_message.data = message.data; attack_message.key1 = message.key1
			-> attack_message.key2 = K_Charlie;
		:: (message.key2 != None && message.key1 == None)
	    -> attack_message.data = message.data; attack_message.key2 = message.key2
			-> attack_message.key1 = K_Charlie;
		/* If the message is readable the attack is happy */
		:: ((message.key1 == K_Charlie && message.key2 == None) || (message.key2 == K_Charlie && message.key1 == None))
			-> charlie_read = 1;
		fi;


		/* sends the message to bob */
		charlie_to_bob!message;
	};

	:: atomic {
		/* case two: reads from bob */
		charlie_to_bob?message;

		/* sends the message to alice */
		if
		:: attacker == 1 -> alice_to_charlie!attack_message
		:: else -> alice_to_charlie!message
		fi
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
		run Charlie(1); // Replace 1 by 0 to get a passive Charlie
		run Bob()
	}
}
