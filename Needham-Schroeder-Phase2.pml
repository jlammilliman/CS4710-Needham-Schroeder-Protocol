/*
    CS 4710 - Model Driven Software Development
    FALL 2022 - R01
    SPIN Project 2 - Needham-Schroeder (NS) Protocol
    Phase 2 : Inturder
    Last Modified On: 11/04/2022

    Team Members: 
        - Jack Snowden
        - Justin Milliman

    ============ Project Description ============
    Security protocols provide a medium for communication over the internet. Once
    a connection is authenticated, parties should be able to communicate to each-
    other without fear of being intercepted, potentially exposing sensitive info.

    Needham-Schroeder (NS) Protocol is a well-known algorothm for establishing a 
    secure connection between parties. This program implements a basic version of
    the Needham-Schroeder Protocol. 

    The project shall be conducted in two phases. This is Phase 2 : Inturder
    
    Phase 2:
     -> Add an intruder to the Basic Model (For details see the Phase 1 specification)
     model who's goal is to intercept but not decrypt any information
     -> Simulate the model and observe the outpt sequence
     -> Verify that Alice and Bob botth terminate gracefully
     -> Explore what happens when we manipulate the fairness policy

    ============ Intruder Model ================
    In the next step of this project, we would like to study the impact of an 
    intruder on the authenticity and confidentiality of the NS protocol. The intruder
    has its own public key, ID and nonce. The intruder can non-deterministically 
    intercept a packet and extract its three fields. Note that, in this model the 
    intruder can only distinguish what the different fields of an encrypted message 
    are and store them; it cannot decrypt the message components and cannot know the 
    nonces of Alice and Bob. Then, it can non-deterministically either forward the 
    intercepted packet to an arbitrarily picked agent, or put together a totally new 
    packet (using the stored values) and send it to an arbitrarily selected agent. 
    Notice that, before sending a message out, the intruder randomly decides which 
    message type (out of the three types in the NS protocol) it would like to send out.

*/

// ============= SETUP ========================

// Construct our mtypes
mtype : packet = { payload, msgNumAndType, rId } 
mtype : client = { alice, bob }                                         // Define partisans
mtype : msgCnt = { null, agentAlice, agentBob, nonceAlice, nonceBob }   // define msg container
mtype : msgKey = { keyAlice, keyBob }

// Define the struct for our messages
typedef encryptedMsg { mtype : msgCnt container1, container2; mtype : msgKey key }

// Define Sync channel
chan network = [0] of {
    mtype : msgType,
    mtype : client, // Used to specify intended recipient
    encryptedMsg
}

// Setup for LTL 
mtype : client verifiedAlice
mtype : client verifiedBob
mtype : msgCnt nonceStoredAlice, nonceStoredBob // Unused in Phase 1, will be used in Phase 2. LTL short circuits to true 


// ============= DEFINE LTL ===================
// -> We want to validate that Alice and Bob communicate without interuption

// Iff verifiedClient != 0, we received something (meaning we succsessfully sent and received a message)
#define AliceIsVerified ( verifiedAlice != 0 )
#define BobIsVerified   ( verifiedBob != 0 )

// End in a state where the received packet is from the intended party
#define AliceReceivedBob ( verifiedAlice == bob )
#define BobReceivedAlice ( verifiedBob == alice )

// End in a state where the received nonce is from the intended party
#define NonceStoredVerifiedAlice    ( nonceStoredAlice != nonceAlice )
#define NonceStoredVerifiedBob      ( nonceStoredBob != nonceBob )

// Both parties received their packet from the intended party and died gracefully
#define PartiesTerminated ( AliceIsVerified && BobIsVerified )

ltl IsEncrypted     { [] ( PartiesTerminated  -> ( AliceReceivedBob <-> BobReceivedAlice) ) }   // -N IsEncrptyed 
ltl NoInteruption   { [] ( PartiesTerminated  -> ( AliceReceivedBob && BobReceivedAlice ) ) }   // -N NoInteruption
ltl AliceIsSecure   { [] ( AliceReceivedBob   -> NonceStoredVerifiedAlice ) }
ltl BobIsSecure     { [] ( BobReceivedAlice   -> NonceStoredVerifiedBob ) }
ltl Termination     { [] ( PartiesTerminated )}


// ============= DEFINE PARTISANS ============= 

// ============= ALICE ======================== 
active proctype Alice() {
    mtype : msgCnt nonce = nonceAlice 
    mtype : msgKey key = keyAlice
    encryptedMsg msgOut, msgIn      // create two encrypted objects
    mtype : client receiver         // open a receiving client

    // Get in the mood to send a message to our betrothed
    atomic {
        verifiedAlice = 0 // arbitrary value -> 0 allows simple comparison to see if we received anything
        if
            :: receiver = bob
        fi
    }

    // Initiate contact with our betrothed -> SEND IT <3
    atomic {
        msgOut.container1 = agentAlice
        msgOut.container2 = nonce
        if
            :: receiver == bob -> msgOut.key = keyBob
        fi
        network ! payload(receiver, msgOut)
    }

    // If we detect our own message in the network, ignore it
    atomic {
        network ? msgNumAndType(alice, msgIn)
        
        if  // If it's our key, ignore the message
            :: msgIn.key == key ->
                skip
            :: else ->
                // printf("Invalid Key for A\n") // Unreachable state
                goto err
        fi

        if  // If it's our nonce, ignore the message
            :: msgIn.container1 == nonce ->
                skip
            :: else ->
                // printf("Invalid Nonce for A\n") // Unreachable staet
                goto err
        fi
        verifiedAlice = receiver 
    }

    // Wait eagerly for incoming mail, once we get it, open it immediately to see if it's from our betrothed
    atomic {
        msgOut.container1 = msgIn.container2
        msgOut.container2 = null
        if
            :: receiver == bob ->
                msgOut.key = keyBob
        fi
        network ! rId(receiver, msgOut) // Congrats, we have a friend
    }
    goto end
err:
    // printf("err in Alice") // Unreachable state
end:
}

// ============= BOB ==========================
active proctype Bob() {
    mtype : msgCnt nonce = nonceBob
    mtype : msgKey key = keyBob
    encryptedMsg msgOut, msgIn      // create two encrypted objects
    mtype : client receiver         // open a receiving client

    // Mega Chad's don't make the first move
    verifiedBob = 0
    
    // Catch and ignore the third correspondance
    atomic {
        network ? payload(bob, msgIn)
        if
            :: msgIn.key == key ->
                skip
            :: else ->
                // printf("Invalid Key for B: %e\n", msgIn.key) // Unreachable state
                goto err
        fi
    }

    // If it's Alice, respond
    atomic {
        if
            :: msgIn.container1 == agentAlice ->
                receiver = alice
                msgOut.key = keyAlice
        fi
        msgOut.container1 = msgIn.container2
        msgOut.container2 = nonce
        network ! msgNumAndType(receiver, msgOut)
    }

    // If we detect our response, ignore it
    atomic {
        network ? rId(bob, msgIn)
        if
            :: msgIn.key == key ->
                skip
            :: else ->
                // printf("Invalid Key for B\n") // Unreachable state
                goto err
        fi
        if
            :: msgIn.container1 == nonce ->
                skip
            :: else ->
                // printf("Invalid Nonce for B\n") // Unreachable state
                goto err
        fi

        verifiedBob = receiver
    }
    goto end
err:
    // printf("err in Bob") // Unreachable state
end:
}
