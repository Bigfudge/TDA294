mtype = {ok, err, msg1, msg2, msg3, keyA, keyB, keyI,
  agentA, agentB, agentI, nonceA, nonceB, nonceI };

typedef Crypt { mtype key, content1, content2, content3 };

chan network = [0] of {mtype, /* msg# */
  mtype, /* receiver */
  Crypt
};

/* global variables for verification*/
mtype partnerA, partnerB;
mtype statusA = err;
mtype statusB = err;
bool knows_nonceA = false;
bool knows_nonceB = false;

/* Agent (A)lice */
active proctype Alice() {
  /* local variables */

  mtype pkey;      /* the other agent's public key                 */
  mtype pnonce;    /* nonce that we receive from the other agent   */
  Crypt messageAB; /* our encrypted message to the other party     */
  Crypt data;      /* received encrypted message                   */


  /* Initialization - Task 4 */
  if
    :: true -> partnerA = agentB; pkey = keyB;
    :: true -> partnerA = agentI; pkey = keyI;
  fi

  /* Prepare the first message */

  messageAB.key = pkey;
  messageAB.content1 = agentA;
  messageAB.content2 = nonceA;
  messageAB.content3 = 0; /* Content1 already provides identity */

  /* Send the first message to the other party */

  network ! msg1 (partnerA, messageAB);

  /* Wait for an answer. Observe that we are pattern-matching on the
     messages that start with msg2 and agentA, that is, we block until
     we see a message with values msg2 and agentA as the first and second
     components. The third component is copied to the variable data. */

  network ? (msg2, agentA, data);

  /* We proceed only if the key field of the data matches keyA and the
     received nonce is the one that we have sent earlier; block
     otherwise.  */
  /* Addendum. We only accept the result if the encrypted identity is our
     intended partner. */

  (data.key == keyA) && (data.content1 == nonceA) && (data.content3 == partnerA);

  /* Obtain Bob's nonce */

  pnonce = data.content2;

  /* Prepare the last message */
  messageAB.key = pkey;
  messageAB.content1 = pnonce;
  messageAB.content2 = 0;  /* content2 is not used in the last message,
                              just set it to 0 */
  messageAB.content3 = 0;

  /* Send the prepared messaage */
  network ! msg3 (partnerA, messageAB);

  /* and last - update the auxilary status variable */
  statusA = ok;
}

active proctype Bob() {
  /* local variables */
  mtype pkey;      /* the other agent's public key                 */
  mtype pnonce;    /* nonce that we receive from the other agent   */
  Crypt messageAB; /* our encrypted message to the other party     */
  Crypt data;      /* received encrypted message                   */

  /* Initialization  */
  partnerB = agentA;
  pkey     = keyA;

  /* Wait for initial message from our partner */
  network ? (msg1, agentB, data)

  /* Verify message was for us and encrypted with the correct key */
  (data.key == keyB) && (data.content1 == partnerB);

  /* Store their nonce */
  pnonce = data.content2;

  /* Reply with their nonce (authentication) and our nonce (confidentiality) */
  messageAB.key = pkey;
  messageAB.content1 = pnonce;
  messageAB.content2 = nonceB;
  messageAB.content3 = agentB; /* Append identity to msg2 */

  /* Send message */
  network ! msg2 (partnerB, messageAB)

  /* Wait for nonce verification message (final authentication) */
  network ? (msg3, agentB, data)

  /* Verify message */
  (data.key == keyB) && (data.content1 == nonceB);

  /* Done! Channel ready */
  statusB = ok;
}

active proctype Intruder() {
  mtype msg, recpt;
  Crypt data, intercepted;
  do
    :: network ? (msg, _, data) ->

       if /* perhaps store the message */
         :: intercepted.key   = data.key;
            intercepted.content1 = data.content1;
            intercepted.content2 = data.content2;
            intercepted.content3 = data.content3;
         :: skip;
       fi ;

       /* .. receive messages encrypted with their key, they should
          be able to decrypt and access the content of those
          (and only those) messages. */

       /* To add the possibility of decryption extend the intruder with
          __another__ if block which checks the key of the __intercepted data__.
          If the key matches with the one of the intruder, proceed to
          check the content; __skip otherwise__. */
       if
         :: intercepted.key == keyI ->
            if
            /* ... set these variables (knows_nonceX) to true only when
               successful decryption of an intercepted message yields
               nonceA or nonceB. */
              :: intercepted.content2 == nonceA -> knows_nonceA = true;
              :: intercepted.content2 == nonceB -> knows_nonceB = true;
              :: intercepted.content1 == nonceA -> knows_nonceA = true;
              :: intercepted.content1 == nonceB -> knows_nonceB = true;
            fi
         :: skip;
       fi ;

    :: /* Replay or send a message */
       if /* choose message type */
         :: msg = msg1;
         :: msg = msg2;
         :: msg = msg3;
       fi ;
       if /* choose a recepient */
         :: recpt = agentA;
         :: recpt = agentB;
       fi ;
       if /* replay intercepted message or assemble it */
         :: data.key    = intercepted.key;
            data.content1  = intercepted.content1;
            data.content2  = intercepted.content2;
            data.content3  = intercepted.content3;
         :: if /* assemble content1 */
              :: data.content1 = agentA;
              :: data.content1 = agentB;
              :: data.content1 = agentI;
              :: data.content1 = nonceI;
              /* When assembling content of the message that the intruder
                 sends, use the variables knows_nonceA and knows_nonceB so
                 that if these variables are true then the attacker may use
                 the corresponding nonce. */
              :: knows_nonceA -> data.content1 = nonceA;
              :: knows_nonceB -> data.content1 = nonceB;
            fi ;
            if /* assemble content3 */
              :: data.content3 = agentA;
              :: data.content3 = agentB;
              :: data.content3 = agentI;
            fi ;
            if /* assemble key */
              :: data.key = keyA;
              :: data.key = keyB;
              :: data.key = keyI;
            fi ;
            /* ... if intruder is composing msg3 then content2 (which is not
               used for messages of type msg3) of the assembled message could
               be just set to 0. */
            if
              :: msg == msg3 -> data.content2 = 0;
              :: skip;
            fi ;
            if
              /* When assembling content of the message that the intruder
                 sends, use the variables knows_nonceA and knows_nonceB so
                 that if these variables are true then the attacker may use
                 the corresponding nonce. */
              :: knows_nonceA -> data.content2 = nonceA;
              :: knows_nonceB -> data.content2 = nonceB;
              :: data.content2 = nonceI;
            fi ;
       fi ;
      network ! msg (recpt, data);
  od
}

ltl propA {
  []((statusA == ok && partnerA == agentB) -> !knows_nonceA)
}

ltl propB {
  []((statusB == ok && partnerB == agentA) -> !knows_nonceB)
}

ltl propAB {
  []((statusA == ok && statusB == ok) -> (partnerA == agentB && partnerB == agentA))
}

