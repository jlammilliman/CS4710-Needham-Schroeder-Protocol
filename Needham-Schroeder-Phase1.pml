/*
    CS 4710 - Model Driven Software Development
    FALL 2022 - R01
    SPIN Project 2 - Needham-Schroeder (NS) Protocol
    Phase 1 : Basic Model
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

    The project shall be conducted in two phases. This is Phase 1 : Basic Model
    
    Phase 1:
     -> Implements the 'Basic Model.' Assume Alice is the initiator.
     -> Simulate the model and observe the output sequence
     -> Verify that Alice and Bob both terminate gracefully
     -> Explore what happens when we manipulate the fairness policy

    ============ Basic Model ===================
        We would like to perform the modeling and verification of the NS protocol  
    in an incremental fashion, where we start from a simple model that contains 
    only Alice and Bob represented as two separate proctypes. We model the 
    communication network as a channel shared by Alice and Bob. To keep the state 
    space small, we consider a synchronous channel through which Alice and Bob 
    can communicate. Another abstraction concern is regarding client IDs, nonces 
    and keys. In real-world systems, these are all multi-bit numbers. However, to 
    keep the state space small and to simplify our model, we model them as 'mtype.' 
    We model encrypted messages as a user-defined data type that includes three
    fields, all of type ‘’mtype’. These fields respectively represent a key, and 
    two other pieces of data, each one of them being anything such as nonce or ID. 

    The synchronous channel exchanges packets that have three fields: 
        - payload -> an encrypted message
        - a message number/type
        - the ID of the receiver 

    ...notice that, the NS protocol includes THREE rendezvous between Alice and Bob. 
    If they can finish these three rendezvous, then we can say that the protocol is 
    correct. You may consider each rendezvous carrying a specific message. This way
    you would have three types of messages.

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
    mtype : packet,
    mtype : client, // Used to specify intended recipient
    encryptedMsg
}

// Setup for LTL 
mtype : client verifiedAlice
mtype : client verifiedBob

// ============= DEFINE LTL ===================
// -> We want to validate that Alice and Bob communicate without interuption

// Iff verifiedClient != 0, we received something (meaning we succsessfully sent and received a message)
#define AliceIsVerified ( verifiedAlice != 0 )
#define BobIsVerified   ( verifiedBob != 0 )

// End in a state where the received packet count is from the intended party
#define AliceReceivedBob ( verifiedAlice == bob ) // Alice should receive 1, send 2
#define BobReceivedAlice ( verifiedBob == alice ) // Bob should receive 2, send 1

// Both parties received their packet from the intended party and died gracefully
#define PartiesTerminated ( AliceIsVerified && BobIsVerified )

// ltl IsEncrypted     { [] ( PartiesTerminated  -> ( AliceReceivedBob <-> BobReceivedAlice) ) }
// ltl NoInteruption   { [] ( PartiesTerminated  -> ( AliceReceivedBob && BobReceivedAlice ) ) }
ltl Termination     { [] <> ( PartiesTerminated ) }


// ============= DEFINE PARTISANS =============  

// ============= ALICE ======================== 
active proctype Alice() {
    mtype : msgCnt nonce = nonceAlice 
    mtype : msgKey key = keyAlice
    encryptedMsg msgOut, msgIn      // create two encrypted objects
    mtype : client receiver         // open a receiving client

    // Get in the mood to send a message to our betrothed
    atomic {
        verifiedAlice = 0 // We have received nothing
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
                goto err
        fi

        if  // If it's our nonce, ignore the message
            :: msgIn.container1 == nonce ->
                skip
            :: else ->
                goto err
        fi
        verifiedAlice = receiver // If it's the first response from Bob, send something again
    }

    // Wait eagerly for incoming mail, once we get it, open it immediately to see if it's from our betrothed
    atomic {
        msgOut.container1 = msgIn.container2
        msgOut.container2 = null
        if
            :: receiver == bob ->
                msgOut.key = keyBob
        fi
        network ! rId(receiver, msgOut) // Congrats, we have a friend. Send him a message to tell him how excited we are
    }
    // goto end
err:
    // printf("Alice go err") // Unreachable state
// end:
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
                goto err
        fi
        if
            :: msgIn.container1 == nonce ->
                skip
            :: else ->
                goto err
        fi

        verifiedBob = receiver
    }
    // goto end
err:
    // printf("Bob go err") // Unreachable state
// end:
}

// ============= INTERCEPTOR ==================


// He go here