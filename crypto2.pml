mtype = { K_Alice, K_Bob, K_Charlie, None };

typedef msg {
	int data;
	mtype key1;
	mtype key2
};

chan secret = [1] of { msg };
byte bob_read = 0;
byte charlie_read = 0;

proctype Alice(int secret_data) {
  msg message;
  do
  /* The channel is empty, Alice sends her message */
  :: atomic {
    empty(secret) ->
    message.data = secret_data; message.key1 = K_Alice; message.key2 = None
    -> bob_read = 0
		-> secret!message
  }

  :: atomic {
    secret?message;

		if
		/* Alice removes her own key if there's another key */
		:: (message.key1 == K_Alice && message.key2 != None)
			-> message.key1 = None -> secret!message;
		:: (message.key2 == K_Alice && message.key1 != None)
	    -> message.key2 = None -> secret!message;

		/* default case: Alice re-emits the message without changing it */
		:: secret!message;
		fi
  }
  od
}

proctype Bob() {
  msg message;
  do
	:: atomic {
		/* first read the message */
		secret?message;
		if

		/* There is only one key but not his, Bob add its own*/
	  :: (message.key1 != None && message.key1 != K_Bob && message.key2 == None)
	    -> message.key2 = K_Bob -> secret!message;
	  :: (message.key2 != None && message.key2 != K_Bob && message.key1 == None)
	    -> message.key1 = K_Bob -> secret!message;

		/* There is only Bob's key: Bob reads the message */
		:: (message.key1 == K_Bob && message.key2 == None) || (message.key2 == K_Bob && message.key1 == None)
			-> bob_read = 1;

		/* default case: Bob just re-emits the message unchanged */
		:: secret!message;
		fi
	}
  od
}

init {
	run Alice(867864);
	run Bob();
}
