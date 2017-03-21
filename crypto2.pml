mtype = { K_Alice, K_Bob, K_Charlie, None };

typedef msg {
	int data;
	mtype key1;
	mtype key2
};

chan secret = [0] of { msg };
byte bob_read = 0;
byte charlie_read = 0;

ltl protocol_ok { [] (<> bob_read) };

proctype Alice(int secret_data) {
  msg message;
  do
  /* The channel is empty, Alice sends her message */
  :: atomic {
    message.data = secret_data; message.key1 = K_Alice; message.key2 = None
    -> secret!message
    -> bob_read = 0
  }

  /* Alice removes her own key if there's another key */
  :: atomic {
    secret?message
    -> (message.key1 == K_Alice && message.key2 != None)
    -> message.key1 = None -> secret!message
  }
  :: atomic {
    secret?message
    -> (message.key2 == K_Alice && message.key1 != None)
    -> message.key2 = None -> secret!message
  }
  od
}

proctype Bob() {
  msg message;
  do
  /* There is only one key but not his, Bob add its own*/
  :: atomic {
    secret?message
    -> (message.key1 != None && message.key1 != K_Bob && message.key2 == None)
    -> message.key2 = K_Bob -> secret!message
  }
  :: atomic {
    secret?message
    -> (message.key2 != None && message.key2 != K_Bob && message.key1 == None)
    -> message.key1 = K_Bob -> secret!message
  }
  /* There is only Bob's key: Bob reads the message */
  :: atomic {
    secret?message
    -> (message.key1 == K_Bob && message.key2 == None)
    -> bob_read = 1
  }
  :: atomic {
    secret?message
    -> (message.key2 == K_Bob && message.key1 == None)
    -> bob_read = 1
  }
  od
}

init {
     run Alice(867864);
     run Bob();
}
