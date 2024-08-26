// This file is generated by genkeywords.cxx. DO NOT EDIT DIRECTLY!
#include "keywords.h"
long fd_webserver_json_keyword(const char* keyw, unsigned long keyw_sz) {
  switch (keyw_sz) {
  case 2:
    if ((*(unsigned long*)&keyw[0] & 0xFFFFUL) == 0x6469UL) {
      return KEYW_JSON_ID; // "id"
    }
  break;
  case 4:
    if ((*(unsigned long*)&keyw[0] & 0xFFFFFFFFUL) == 0x746E696DUL) {
      return KEYW_JSON_MINT; // "mint"
    }
  break;
  case 5:
    switch (keyw[0]) {
    case 'b':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFUL) == 0x73657479UL) {
        return KEYW_JSON_BYTES; // "bytes"
      }
      break;
    case 'e':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFUL) == 0x68636F70UL) {
        return KEYW_JSON_EPOCH; // "epoch"
      }
      break;
    case 'l':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFUL) == 0x74696D69UL) {
        return KEYW_JSON_LIMIT; // "limit"
      }
      break;
    }
  break;
  case 6:
    switch (keyw[0]) {
    case 'l':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFUL) == 0x6874676E65UL) {
        return KEYW_JSON_LENGTH; // "length"
      }
      break;
    case 'm':
      if (keyw[1] == 'e') {
        switch (keyw[2]) {
        case 'm':
          if ((*(unsigned long*)&keyw[3] & 0xFFFFFFUL) == 0x706D63UL) {
            return KEYW_JSON_MEMCMP; // "memcmp"
          }
          break;
        case 't':
          if ((*(unsigned long*)&keyw[3] & 0xFFFFFFUL) == 0x646F68UL) {
            return KEYW_JSON_METHOD; // "method"
          }
          break;
        }
      }
      break;
    case 'o':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFUL) == 0x7465736666UL) {
        return KEYW_JSON_OFFSET; // "offset"
      }
      break;
    case 'p':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFUL) == 0x736D617261UL) {
        return KEYW_JSON_PARAMS; // "params"
      }
      break;
    }
  break;
  case 7:
    switch (keyw[0]) {
    case 'r':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFFFUL) == 0x736472617765UL) {
        return KEYW_JSON_REWARDS; // "rewards"
      }
      break;
    case 'j':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFFFUL) == 0x6370726E6F73UL) {
        return KEYW_JSON_JSONRPC; // "jsonrpc"
      }
      break;
    case 'f':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFFFUL) == 0x737265746C69UL) {
        return KEYW_JSON_FILTERS; // "filters"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'F':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFUL) == 0x736565UL) {
            return KEYW_RPCMETHOD_GETFEES; // "getFees"
          }
          break;
        case 'S':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFUL) == 0x746F6CUL) {
            return KEYW_RPCMETHOD_GETSLOT; // "getSlot"
          }
          break;
        }
      }
      break;
    }
  break;
  case 8:
    switch (keyw[0]) {
    case 'd':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFFFFFUL) == 0x657A6953617461UL) {
        return KEYW_JSON_DATASIZE; // "dataSize"
      }
      break;
    case 'e':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFFFFFUL) == 0x676E69646F636EUL) {
        return KEYW_JSON_ENCODING; // "encoding"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFFFFFUL) == 0x6B636F6C427465UL) {
        return KEYW_RPCMETHOD_GETBLOCK; // "getBlock"
      }
      break;
    case 'i':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFFFFFFFFFFFUL) == 0x797469746E6564UL) {
        return KEYW_JSON_IDENTITY; // "identity"
      }
      break;
    }
  break;
  case 9:
    switch (keyw[0]) {
    case 'd':
      if (*(unsigned long*)&keyw[1] == 0x6563696C53617461UL) {
        return KEYW_JSON_DATASLICE; // "dataSlice"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'B':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFFFUL) == 0x736B636F6CUL) {
            return KEYW_RPCMETHOD_GETBLOCKS; // "getBlocks"
          }
          break;
        case 'H':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFFFUL) == 0x68746C6165UL) {
            return KEYW_RPCMETHOD_GETHEALTH; // "getHealth"
          }
          break;
        case 'S':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFFFUL) == 0x796C707075UL) {
            return KEYW_RPCMETHOD_GETSUPPLY; // "getSupply"
          }
          break;
        }
      }
      break;
    case 'p':
      if (*(unsigned long*)&keyw[1] == 0x64496D6172676F72UL) {
        return KEYW_JSON_PROGRAMID; // "programId"
      }
      break;
    }
  break;
  case 10:
    switch (keyw[0]) {
    case 'c':
      if (*(unsigned long*)&keyw[1] == 0x6E656D74696D6D6FUL && keyw[9] == 't') {
        return KEYW_JSON_COMMITMENT; // "commitment"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'B':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFFFFFUL) == 0x65636E616C61UL) {
            return KEYW_RPCMETHOD_GETBALANCE; // "getBalance"
          }
          break;
        case 'V':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFFFFFUL) == 0x6E6F69737265UL) {
            return KEYW_RPCMETHOD_GETVERSION; // "getVersion"
          }
          break;
        }
      }
      break;
    case 'm':
      if (*(unsigned long*)&keyw[1] == 0x6569727465527861UL && keyw[9] == 's') {
        return KEYW_JSON_MAXRETRIES; // "maxRetries"
      }
      break;
    case 'v':
      if (*(unsigned long*)&keyw[1] == 0x656B62755065746FUL && keyw[9] == 'y') {
        return KEYW_JSON_VOTEPUBKEY; // "votePubkey"
      }
      break;
    }
  break;
  case 11:
    if (*(unsigned long*)&keyw[0] == 0x746E656449746567UL && (*(unsigned long*)&keyw[8] & 0xFFFFFFUL) == 0x797469UL) {
      return KEYW_RPCMETHOD_GETIDENTITY; // "getIdentity"
    }
  break;
  case 12:
    if ((*(unsigned long*)&keyw[0] & 0xFFFFFFUL) == 0x746567UL) {
      switch (keyw[3]) {
      case 'B':
        if (*(unsigned long*)&keyw[4] == 0x656D69546B636F6CUL) {
          return KEYW_RPCMETHOD_GETBLOCKTIME; // "getBlockTime"
        }
        break;
      case 'E':
        if (*(unsigned long*)&keyw[4] == 0x6F666E4968636F70UL) {
          return KEYW_RPCMETHOD_GETEPOCHINFO; // "getEpochInfo"
        }
        break;
      }
    }
  break;
  case 13:
    switch (keyw[0]) {
    case 'g':
      if (*(unsigned long*)&keyw[1] == 0x654C746F6C537465UL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFUL) == 0x72656461UL) {
        return KEYW_RPCMETHOD_GETSLOTLEADER; // "getSlotLeader"
      }
      break;
    case 'l':
      if (*(unsigned long*)&keyw[1] == 0x637362755373676FUL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFUL) == 0x65626972UL) {
        return KEYW_WS_METHOD_LOGSSUBSCRIBE; // "logsSubscribe"
      }
      break;
    case 'r':
      if (*(unsigned long*)&keyw[1] == 0x6373627553746F6FUL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFUL) == 0x65626972UL) {
        return KEYW_WS_METHOD_ROOTSUBSCRIBE; // "rootSubscribe"
      }
      break;
    case 's':
      switch (keyw[1]) {
      case 'k':
        if (*(unsigned long*)&keyw[2] == 0x696C666572507069UL && (*(unsigned long*)&keyw[10] & 0xFFFFFFUL) == 0x746867UL) {
          return KEYW_SKIPPREFLIGHT; // "skipPreflight"
        }
        break;
      case 'l':
        if (*(unsigned long*)&keyw[2] == 0x726373627553746FUL && (*(unsigned long*)&keyw[10] & 0xFFFFFFUL) == 0x656269UL) {
          return KEYW_WS_METHOD_SLOTSUBSCRIBE; // "slotSubscribe"
        }
        break;
      }
      break;
    case 'v':
      if (*(unsigned long*)&keyw[1] == 0x637362755365746FUL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFUL) == 0x65626972UL) {
        return KEYW_WS_METHOD_VOTESUBSCRIBE; // "voteSubscribe"
      }
      break;
    }
  break;
  case 14:
    switch (keyw[0]) {
    case 'b':
      if (*(unsigned long*)&keyw[1] == 0x736275536B636F6CUL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFUL) == 0x6562697263UL) {
        return KEYW_WS_METHOD_BLOCKSUBSCRIBE; // "blockSubscribe"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'A':
          if (*(unsigned long*)&keyw[4] == 0x6E49746E756F6363UL && (*(unsigned long*)&keyw[12] & 0xFFFFUL) == 0x6F66UL) {
            return KEYW_RPCMETHOD_GETACCOUNTINFO; // "getAccountInfo"
          }
          break;
        case 'B':
          if (*(unsigned long*)&keyw[4] == 0x676965486B636F6CUL && (*(unsigned long*)&keyw[12] & 0xFFFFUL) == 0x7468UL) {
            return KEYW_RPCMETHOD_GETBLOCKHEIGHT; // "getBlockHeight"
          }
          break;
        case 'G':
          if (*(unsigned long*)&keyw[4] == 0x6148736973656E65UL && (*(unsigned long*)&keyw[12] & 0xFFFFUL) == 0x6873UL) {
            return KEYW_RPCMETHOD_GETGENESISHASH; // "getGenesisHash"
          }
          break;
        case 'S':
          if (*(unsigned long*)&keyw[4] == 0x656461654C746F6CUL && (*(unsigned long*)&keyw[12] & 0xFFFFUL) == 0x7372UL) {
            return KEYW_RPCMETHOD_GETSLOTLEADERS; // "getSlotLeaders"
          }
          break;
        case 'T':
          switch (keyw[4]) {
          case 'o':
            if (*(unsigned long*)&keyw[5] == 0x6C707075536E656BUL && keyw[13] == 'y') {
              return KEYW_RPCMETHOD_GETTOKENSUPPLY; // "getTokenSupply"
            }
            break;
          case 'r':
            if (*(unsigned long*)&keyw[5] == 0x6F69746361736E61UL && keyw[13] == 'n') {
              return KEYW_RPCMETHOD_GETTRANSACTION; // "getTransaction"
            }
            break;
          }
          break;
        }
      }
      break;
    case 'm':
      if (*(unsigned long*)&keyw[1] == 0x7865746E6F436E69UL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFUL) == 0x746F6C5374UL) {
        return KEYW_JSON_MINCONTEXTSLOT; // "minContextSlot"
      }
      break;
    case 'r':
      if (*(unsigned long*)&keyw[1] == 0x6941747365757165UL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFUL) == 0x706F726472UL) {
        return KEYW_RPCMETHOD_REQUESTAIRDROP; // "requestAirdrop"
      }
      break;
    }
  break;
  case 15:
    switch (keyw[0]) {
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'C':
          if (*(unsigned long*)&keyw[4] == 0x6F4E72657473756CUL && (*(unsigned long*)&keyw[12] & 0xFFFFFFUL) == 0x736564UL) {
            return KEYW_RPCMETHOD_GETCLUSTERNODES; // "getClusterNodes"
          }
          break;
        case 'S':
          if (*(unsigned long*)&keyw[4] == 0x53746F687370616EUL && (*(unsigned long*)&keyw[12] & 0xFFFFFFUL) == 0x746F6CUL) {
            return KEYW_RPCMETHOD_GETSNAPSHOTSLOT; // "getSnapshotSlot"
          }
          break;
        case 'V':
          if (*(unsigned long*)&keyw[4] == 0x756F63634165746FUL && (*(unsigned long*)&keyw[12] & 0xFFFFFFUL) == 0x73746EUL) {
            return KEYW_RPCMETHOD_GETVOTEACCOUNTS; // "getVoteAccounts"
          }
          break;
        }
      }
      break;
    case 'l':
      if (*(unsigned long*)&keyw[1] == 0x6275736E5573676FUL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFFFUL) == 0x656269726373UL) {
        return KEYW_WS_METHOD_LOGSUNSUBSCRIBE; // "logsUnsubscribe"
      }
      break;
    case 'r':
      switch (keyw[1]) {
      case 'e':
        if (*(unsigned long*)&keyw[2] == 0x636F6C42746E6563UL && (*(unsigned long*)&keyw[10] & 0xFFFFFFFFFFUL) == 0x687361686BUL) {
          return KEYW_JSON_RECENTBLOCKHASH; // "recentBlockhash"
        }
        break;
      case 'o':
        if (*(unsigned long*)&keyw[2] == 0x736275736E55746FUL && (*(unsigned long*)&keyw[10] & 0xFFFFFFFFFFUL) == 0x6562697263UL) {
          return KEYW_WS_METHOD_ROOTUNSUBSCRIBE; // "rootUnsubscribe"
        }
        break;
      }
      break;
    case 's':
      switch (keyw[1]) {
      case 'e':
        if (*(unsigned long*)&keyw[2] == 0x61736E617254646EUL && (*(unsigned long*)&keyw[10] & 0xFFFFFFFFFFUL) == 0x6E6F697463UL) {
          return KEYW_RPCMETHOD_SENDTRANSACTION; // "sendTransaction"
        }
        break;
      case 'l':
        if (*(unsigned long*)&keyw[2] == 0x736275736E55746FUL && (*(unsigned long*)&keyw[10] & 0xFFFFFFFFFFUL) == 0x6562697263UL) {
          return KEYW_WS_METHOD_SLOTUNSUBSCRIBE; // "slotUnsubscribe"
        }
        break;
      }
      break;
    case 'v':
      if (*(unsigned long*)&keyw[1] == 0x6275736E5565746FUL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFFFUL) == 0x656269726373UL) {
        return KEYW_WS_METHOD_VOTEUNSUBSCRIBE; // "voteUnsubscribe"
      }
      break;
    }
  break;
  case 16:
    switch (keyw[0]) {
    case 'a':
      if (*(unsigned long*)&keyw[1] == 0x7553746E756F6363UL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFFFFFUL) == 0x65626972637362UL) {
        return KEYW_WS_METHOD_ACCOUNTSUBSCRIBE; // "accountSubscribe"
      }
      break;
    case 'b':
      if (*(unsigned long*)&keyw[1] == 0x75736E556B636F6CUL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFFFFFUL) == 0x65626972637362UL) {
        return KEYW_WS_METHOD_BLOCKUNSUBSCRIBE; // "blockUnsubscribe"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'E':
          if (*(unsigned long*)&keyw[4] == 0x6568635368636F70UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFUL) == 0x656C7564UL) {
            return KEYW_RPCMETHOD_GETEPOCHSCHEDULE; // "getEpochSchedule"
          }
          break;
        case 'F':
          if (*(unsigned long*)&keyw[4] == 0x73654D726F466565UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFUL) == 0x65676173UL) {
            return KEYW_RPCMETHOD_GETFEEFORMESSAGE; // "getFeeForMessage"
          }
          break;
        case 'I':
          if (*(unsigned long*)&keyw[4] == 0x6E6F6974616C666EUL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFUL) == 0x65746152UL) {
            return KEYW_RPCMETHOD_GETINFLATIONRATE; // "getInflationRate"
          }
          break;
        }
      }
      break;
    case 'i':
      if (*(unsigned long*)&keyw[1] == 0x61686B636F6C4273UL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFFFFFUL) == 0x64696C61566873UL) {
        return KEYW_RPCMETHOD_ISBLOCKHASHVALID; // "isBlockhashValid"
      }
      break;
    case 'p':
      if (*(unsigned long*)&keyw[1] == 0x75536D6172676F72UL && (*(unsigned long*)&keyw[9] & 0xFFFFFFFFFFFFFFUL) == 0x65626972637362UL) {
        return KEYW_WS_METHOD_PROGRAMSUBSCRIBE; // "programSubscribe"
      }
      break;
    }
  break;
  case 17:
    switch (keyw[0]) {
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'C':
          if (*(unsigned long*)&keyw[4] == 0x64656D7269666E6FUL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFUL) == 0x6B636F6C42UL) {
            return KEYW_RPCMETHOD_GETCONFIRMEDBLOCK; // "getConfirmedBlock"
          }
          break;
        case 'L':
          if (*(unsigned long*)&keyw[4] == 0x6863537265646165UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFUL) == 0x656C756465UL) {
            return KEYW_RPCMETHOD_GETLEADERSCHEDULE; // "getLeaderSchedule"
          }
          break;
        }
      }
      break;
    case 'm':
      if (*(unsigned long*)&keyw[1] == 0x654C6D756D696E69UL && *(unsigned long*)&keyw[9] == 0x746F6C5372656764UL) {
        return KEYW_RPCMETHOD_MINIMUMLEDGERSLOT; // "minimumLedgerSlot"
      }
      break;
    }
  break;
  case 18:
    switch (keyw[0]) {
    case 'a':
      if (*(unsigned long*)&keyw[1] == 0x6E55746E756F6363UL && *(unsigned long*)&keyw[9] == 0x6269726373627573UL && keyw[17] == 'e') {
        return KEYW_WS_METHOD_ACCOUNTUNSUBSCRIBE; // "accountUnsubscribe"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'B':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFUL) == 0x6B636F6CUL) {
            switch (keyw[8]) {
            case 'C':
              if (*(unsigned long*)&keyw[9] == 0x6E656D74696D6D6FUL && keyw[17] == 't') {
                return KEYW_RPCMETHOD_GETBLOCKCOMMITMENT; // "getBlockCommitment"
              }
              break;
            case 'P':
              if (*(unsigned long*)&keyw[9] == 0x6F69746375646F72UL && keyw[17] == 'n') {
                return KEYW_RPCMETHOD_GETBLOCKPRODUCTION; // "getBlockProduction"
              }
              break;
            case 's':
              if (*(unsigned long*)&keyw[9] == 0x696D694C68746957UL && keyw[17] == 't') {
                return KEYW_RPCMETHOD_GETBLOCKSWITHLIMIT; // "getBlocksWithLimit"
              }
              break;
            }
          }
          break;
        case 'C':
          if (*(unsigned long*)&keyw[4] == 0x64656D7269666E6FUL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFUL) == 0x736B636F6C42UL) {
            return KEYW_RPCMETHOD_GETCONFIRMEDBLOCKS; // "getConfirmedBlocks"
          }
          break;
        case 'F':
          if (*(unsigned long*)&keyw[4] == 0x6F47657461526565UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFUL) == 0x726F6E726576UL) {
            return KEYW_RPCMETHOD_GETFEERATEGOVERNOR; // "getFeeRateGovernor"
          }
          break;
        case 'I':
          if (*(unsigned long*)&keyw[4] == 0x6E6F6974616C666EUL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFUL) == 0x647261776552UL) {
            return KEYW_RPCMETHOD_GETINFLATIONREWARD; // "getInflationReward"
          }
          break;
        case 'L':
          if (keyw[4] == 'a') {
            switch (keyw[5]) {
            case 'r':
              if (*(unsigned long*)&keyw[6] == 0x6F63634174736567UL && (*(unsigned long*)&keyw[14] & 0xFFFFFFFFUL) == 0x73746E75UL) {
                return KEYW_RPCMETHOD_GETLARGESTACCOUNTS; // "getLargestAccounts"
              }
              break;
            case 't':
              if (*(unsigned long*)&keyw[6] == 0x6B636F6C42747365UL && (*(unsigned long*)&keyw[14] & 0xFFFFFFFFUL) == 0x68736168UL) {
                return KEYW_RPCMETHOD_GETLATESTBLOCKHASH; // "getLatestBlockhash"
              }
              break;
            }
          }
          break;
        case 'P':
          if (*(unsigned long*)&keyw[4] == 0x63416D6172676F72UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFUL) == 0x73746E756F63UL) {
            return KEYW_RPCMETHOD_GETPROGRAMACCOUNTS; // "getProgramAccounts"
          }
          break;
        case 'R':
          if (*(unsigned long*)&keyw[4] == 0x6F6C42746E656365UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFUL) == 0x687361686B63UL) {
            return KEYW_RPCMETHOD_GETRECENTBLOCKHASH; // "getRecentBlockhash"
          }
          break;
        case 'S':
          if (*(unsigned long*)&keyw[4] == 0x69746341656B6174UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFUL) == 0x6E6F69746176UL) {
            return KEYW_RPCMETHOD_GETSTAKEACTIVATION; // "getStakeActivation"
          }
          break;
        }
      }
      break;
    case 'p':
      if (*(unsigned long*)&keyw[1] == 0x6E556D6172676F72UL && *(unsigned long*)&keyw[9] == 0x6269726373627573UL && keyw[17] == 'e') {
        return KEYW_WS_METHOD_PROGRAMUNSUBSCRIBE; // "programUnsubscribe"
      }
      break;
    case 's':
      if (*(unsigned long*)&keyw[1] == 0x65727574616E6769UL && *(unsigned long*)&keyw[9] == 0x6269726373627553UL && keyw[17] == 'e') {
        return KEYW_WS_METHOD_SIGNATURESUBSCRIBE; // "signatureSubscribe"
      }
      break;
    case 't':
      if (*(unsigned long*)&keyw[1] == 0x69746361736E6172UL && *(unsigned long*)&keyw[9] == 0x6C69617465446E6FUL && keyw[17] == 's') {
        return KEYW_JSON_TRANSACTIONDETAILS; // "transactionDetails"
      }
      break;
    }
  break;
  case 19:
    switch (keyw[0]) {
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'M':
          if (*(unsigned long*)&keyw[4] == 0x41656C7069746C75UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFFFUL) == 0x73746E756F6363UL) {
            return KEYW_RPCMETHOD_GETMULTIPLEACCOUNTS; // "getMultipleAccounts"
          }
          break;
        case 'T':
          if (*(unsigned long*)&keyw[4] == 0x69746361736E6172UL && (*(unsigned long*)&keyw[12] & 0xFFFFFFFFFFFFFFUL) == 0x746E756F436E6FUL) {
            return KEYW_RPCMETHOD_GETTRANSACTIONCOUNT; // "getTransactionCount"
          }
          break;
        }
      }
      break;
    case 'p':
      if (*(unsigned long*)&keyw[1] == 0x746867696C666572UL && *(unsigned long*)&keyw[9] == 0x656D74696D6D6F43UL && (*(unsigned long*)&keyw[17] & 0xFFFFUL) == 0x746EUL) {
        return KEYS_PREFLIGHTCOMMITMENT; // "preflightCommitment"
      }
      break;
    case 's':
      if (*(unsigned long*)&keyw[1] == 0x546574616C756D69UL && *(unsigned long*)&keyw[9] == 0x69746361736E6172UL && (*(unsigned long*)&keyw[17] & 0xFFFFUL) == 0x6E6FUL) {
        return KEYW_RPCMETHOD_SIMULATETRANSACTION; // "simulateTransaction"
      }
      break;
    }
  break;
  case 20:
    switch (keyw[0]) {
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'I':
          if (*(unsigned long*)&keyw[4] == 0x6E6F6974616C666EUL && *(unsigned long*)&keyw[12] == 0x726F6E7265766F47UL) {
            return KEYW_RPCMETHOD_GETINFLATIONGOVERNOR; // "getInflationGovernor"
          }
          break;
        case 'M':
          if (*(unsigned long*)&keyw[4] == 0x6E61727465527861UL && *(unsigned long*)&keyw[12] == 0x746F6C5374696D73UL) {
            return KEYW_RPCMETHOD_GETMAXRETRANSMITSLOT; // "getMaxRetransmitSlot"
          }
          break;
        case 'S':
          if (*(unsigned long*)&keyw[4] == 0x65727574616E6769UL && *(unsigned long*)&keyw[12] == 0x7365737574617453UL) {
            return KEYW_RPCMETHOD_GETSIGNATURESTATUSES; // "getSignatureStatuses"
          }
          break;
        }
      }
      break;
    case 's':
      if (*(unsigned long*)&keyw[1] == 0x65727574616E6769UL && *(unsigned long*)&keyw[9] == 0x7263736275736E55UL && (*(unsigned long*)&keyw[17] & 0xFFFFFFUL) == 0x656269UL) {
        return KEYW_WS_METHOD_SIGNATUREUNSUBSCRIBE; // "signatureUnsubscribe"
      }
      break;
    }
  break;
  case 21:
    switch (keyw[0]) {
    case 'g':
      if (*(unsigned long*)&keyw[1] == 0x72685378614D7465UL && *(unsigned long*)&keyw[9] == 0x747265736E496465UL && (*(unsigned long*)&keyw[17] & 0xFFFFFFFFUL) == 0x746F6C53UL) {
        return KEYW_RPCMETHOD_GETMAXSHREDINSERTSLOT; // "getMaxShredInsertSlot"
      }
      break;
    case 's':
      if (*(unsigned long*)&keyw[1] == 0x6164705573746F6CUL && *(unsigned long*)&keyw[9] == 0x6373627553736574UL && (*(unsigned long*)&keyw[17] & 0xFFFFFFFFUL) == 0x65626972UL) {
        return KEYW_WS_METHOD_SLOTSUPDATESSUBSCRIBE; // "slotsUpdatesSubscribe"
      }
      break;
    }
  break;
  case 22:
    if ((*(unsigned long*)&keyw[0] & 0xFFFFFFUL) == 0x746567UL) {
      switch (keyw[3]) {
      case 'F':
        if (*(unsigned long*)&keyw[4] == 0x6961764174737269UL && *(unsigned long*)&keyw[12] == 0x6F6C42656C62616CUL && (*(unsigned long*)&keyw[20] & 0xFFFFUL) == 0x6B63UL) {
          return KEYW_RPCMETHOD_GETFIRSTAVAILABLEBLOCK; // "getFirstAvailableBlock"
        }
        break;
      case 'H':
        if (*(unsigned long*)&keyw[4] == 0x6E53747365686769UL && *(unsigned long*)&keyw[12] == 0x6C53746F68737061UL && (*(unsigned long*)&keyw[20] & 0xFFFFUL) == 0x746FUL) {
          return KEYW_RPCMETHOD_GETHIGHESTSNAPSHOTSLOT; // "getHighestSnapshotSlot"
        }
        break;
      case 'T':
        if (*(unsigned long*)&keyw[4] == 0x6F6363416E656B6FUL && *(unsigned long*)&keyw[12] == 0x6E616C6142746E75UL && (*(unsigned long*)&keyw[20] & 0xFFFFUL) == 0x6563UL) {
          return KEYW_RPCMETHOD_GETTOKENACCOUNTBALANCE; // "getTokenAccountBalance"
        }
        break;
      }
    }
  break;
  case 23:
    switch (keyw[0]) {
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'C':
          if (*(unsigned long*)&keyw[4] == 0x64656D7269666E6FUL && *(unsigned long*)&keyw[12] == 0x746361736E617254UL && (*(unsigned long*)&keyw[20] & 0xFFFFFFUL) == 0x6E6F69UL) {
            return KEYW_RPCMETHOD_GETCONFIRMEDTRANSACTION; // "getConfirmedTransaction"
          }
          break;
        case 'S':
          if (*(unsigned long*)&keyw[4] == 0x65727574616E6769UL && *(unsigned long*)&keyw[12] == 0x72646441726F4673UL && (*(unsigned long*)&keyw[20] & 0xFFFFFFUL) == 0x737365UL) {
            return KEYW_RPCMETHOD_GETSIGNATURESFORADDRESS; // "getSignaturesForAddress"
          }
          break;
        case 'T':
          if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFUL) == 0x6E656B6FUL) {
            switch (keyw[8]) {
            case 'A':
              if (*(unsigned long*)&keyw[9] == 0x4273746E756F6363UL && (*(unsigned long*)&keyw[17] & 0xFFFFFFFFFFFFUL) == 0x72656E774F79UL) {
                return KEYW_RPCMETHOD_GETTOKENACCOUNTSBYOWNER; // "getTokenAccountsByOwner"
              }
              break;
            case 'L':
              if (*(unsigned long*)&keyw[9] == 0x6341747365677261UL && (*(unsigned long*)&keyw[17] & 0xFFFFFFFFFFFFUL) == 0x73746E756F63UL) {
                return KEYW_RPCMETHOD_GETTOKENLARGESTACCOUNTS; // "getTokenLargestAccounts"
              }
              break;
            }
          }
          break;
        }
      }
      break;
    case 's':
      if (*(unsigned long*)&keyw[1] == 0x6164705573746F6CUL && *(unsigned long*)&keyw[9] == 0x6275736E55736574UL && (*(unsigned long*)&keyw[17] & 0xFFFFFFFFFFFFUL) == 0x656269726373UL) {
        return KEYW_WS_METHOD_SLOTSUPDATESUNSUBSCRIBE; // "slotsUpdatesUnsubscribe"
      }
      break;
    }
  break;
  case 24:
    if (*(unsigned long*)&keyw[0] == 0x7254686372616573UL && *(unsigned long*)&keyw[8] == 0x6F69746361736E61UL && *(unsigned long*)&keyw[16] == 0x79726F747369486EUL) {
      return KEYW_JSON_SEARCHTRANSACTIONHISTORY; // "searchTransactionHistory"
    }
  break;
  case 25:
    if (*(unsigned long*)&keyw[0] == 0x656B617453746567UL && *(unsigned long*)&keyw[8] == 0x446D756D696E694DUL && *(unsigned long*)&keyw[16] == 0x6F69746167656C65UL && keyw[24] == 'n') {
      return KEYW_RPCMETHOD_GETSTAKEMINIMUMDELEGATION; // "getStakeMinimumDelegation"
    }
  break;
  case 26:
    if (*(unsigned long*)&keyw[0] == 0x6E656B6F54746567UL && *(unsigned long*)&keyw[8] == 0x73746E756F636341UL && *(unsigned long*)&keyw[16] == 0x6167656C65447942UL && (*(unsigned long*)&keyw[24] & 0xFFFFUL) == 0x6574UL) {
      return KEYW_RPCMETHOD_GETTOKENACCOUNTSBYDELEGATE; // "getTokenAccountsByDelegate"
    }
  break;
  case 27:
    if ((*(unsigned long*)&keyw[0] & 0xFFFFFFUL) == 0x746567UL) {
      switch (keyw[3]) {
      case 'C':
        if (*(unsigned long*)&keyw[4] == 0x64656D7269666E6FUL && *(unsigned long*)&keyw[12] == 0x6957736B636F6C42UL && (*(unsigned long*)&keyw[20] & 0xFFFFFFFFFFFFFFUL) == 0x74696D694C6874UL) {
          return KEYW_RPCMETHOD_GETCONFIRMEDBLOCKSWITHLIMIT; // "getConfirmedBlocksWithLimit"
        }
        break;
      case 'R':
        if ((*(unsigned long*)&keyw[4] & 0xFFFFFFFFFFFFUL) == 0x50746E656365UL) {
          switch (keyw[10]) {
          case 'e':
            if (*(unsigned long*)&keyw[11] == 0x636E616D726F6672UL && *(unsigned long*)&keyw[19] == 0x73656C706D615365UL) {
              return KEYW_RPCMETHOD_GETRECENTPERFORMANCESAMPLES; // "getRecentPerformanceSamples"
            }
            break;
          case 'r':
            if (*(unsigned long*)&keyw[11] == 0x617A697469726F69UL && *(unsigned long*)&keyw[19] == 0x736565466E6F6974UL) {
              return KEYW_RPCMETHOD_GETRECENTPRIORITIZATIONFEES; // "getRecentPrioritizationFees"
            }
            break;
          }
        }
        break;
      }
    }
  break;
  case 28:
    if (*(unsigned long*)&keyw[0] == 0x6143656546746567UL && *(unsigned long*)&keyw[8] == 0x726F74616C75636CUL && *(unsigned long*)&keyw[16] == 0x6B636F6C42726F46UL && (*(unsigned long*)&keyw[24] & 0xFFFFFFFFUL) == 0x68736168UL) {
      return KEYW_RPCMETHOD_GETFEECALCULATORFORBLOCKHASH; // "getFeeCalculatorForBlockhash"
    }
  break;
  case 30:
    if (*(unsigned long*)&keyw[0] == 0x6F7070755378616DUL && *(unsigned long*)&keyw[8] == 0x6E61725464657472UL && *(unsigned long*)&keyw[16] == 0x566E6F6974636173UL && (*(unsigned long*)&keyw[24] & 0xFFFFFFFFFFFFUL) == 0x6E6F69737265UL) {
      return KEYW_JSON_MAXSUPPORTEDTRANSACTIONVERSION; // "maxSupportedTransactionVersion"
    }
  break;
  case 33:
    switch (keyw[0]) {
    case 'e':
      if (*(unsigned long*)&keyw[1] == 0x6F4E6564756C6378UL && *(unsigned long*)&keyw[9] == 0x616C75637269436EUL && *(unsigned long*)&keyw[17] == 0x6F636341676E6974UL && *(unsigned long*)&keyw[25] == 0x7473694C73746E75UL) {
        return KEYW_JSON_EXCLUDENONCIRCULATINGACCOUNTSLIST; // "excludeNonCirculatingAccountsList"
      }
      break;
    case 'g':
      if ((*(unsigned long*)&keyw[1] & 0xFFFFUL) == 0x7465UL) {
        switch (keyw[3]) {
        case 'C':
          if (*(unsigned long*)&keyw[4] == 0x64656D7269666E6FUL && *(unsigned long*)&keyw[12] == 0x727574616E676953UL && *(unsigned long*)&keyw[20] == 0x646441726F467365UL && (*(unsigned long*)&keyw[28] & 0xFFFFFFFFFFUL) == 0x3273736572UL) {
            return KEYW_RPCMETHOD_GETCONFIRMEDSIGNATURESFORADDRESS2; // "getConfirmedSignaturesForAddress2"
          }
          break;
        case 'M':
          if (*(unsigned long*)&keyw[4] == 0x61426D756D696E69UL && *(unsigned long*)&keyw[12] == 0x726F4665636E616CUL && *(unsigned long*)&keyw[20] == 0x6D657845746E6552UL && (*(unsigned long*)&keyw[28] & 0xFFFFFFFFFFUL) == 0x6E6F697470UL) {
            return KEYW_RPCMETHOD_GETMINIMUMBALANCEFORRENTEXEMPTION; // "getMinimumBalanceForRentExemption"
          }
          break;
        }
      }
      break;
    }
  break;
  }
  return KEYW_UNKNOWN;
}
const char* un_fd_webserver_json_keyword(long id) {
  switch (id) {
  case KEYW_JSON_JSONRPC: return "jsonrpc";
  case KEYW_JSON_ID: return "id";
  case KEYW_JSON_METHOD: return "method";
  case KEYW_JSON_PARAMS: return "params";
  case KEYW_JSON_BYTES: return "bytes";
  case KEYW_JSON_COMMITMENT: return "commitment";
  case KEYW_JSON_DATASIZE: return "dataSize";
  case KEYW_JSON_DATASLICE: return "dataSlice";
  case KEYW_JSON_ENCODING: return "encoding";
  case KEYW_JSON_EPOCH: return "epoch";
  case KEYW_JSON_FILTERS: return "filters";
  case KEYW_JSON_IDENTITY: return "identity";
  case KEYW_JSON_LENGTH: return "length";
  case KEYW_JSON_LIMIT: return "limit";
  case KEYW_JSON_MAXSUPPORTEDTRANSACTIONVERSION: return "maxSupportedTransactionVersion";
  case KEYW_JSON_MAXRETRIES: return "maxRetries";
  case KEYW_JSON_MINCONTEXTSLOT: return "minContextSlot";
  case KEYW_JSON_MEMCMP: return "memcmp";
  case KEYW_JSON_MINT: return "mint";
  case KEYW_JSON_OFFSET: return "offset";
  case KEYS_PREFLIGHTCOMMITMENT: return "preflightCommitment";
  case KEYW_JSON_PROGRAMID: return "programId";
  case KEYW_JSON_RECENTBLOCKHASH: return "recentBlockhash";
  case KEYW_JSON_REWARDS: return "rewards";
  case KEYW_JSON_SEARCHTRANSACTIONHISTORY: return "searchTransactionHistory";
  case KEYW_SKIPPREFLIGHT: return "skipPreflight";
  case KEYW_JSON_TRANSACTIONDETAILS: return "transactionDetails";
  case KEYW_JSON_VOTEPUBKEY: return "votePubkey";
  case KEYW_RPCMETHOD_GETACCOUNTINFO: return "getAccountInfo";
  case KEYW_RPCMETHOD_GETBALANCE: return "getBalance";
  case KEYW_RPCMETHOD_GETBLOCK: return "getBlock";
  case KEYW_RPCMETHOD_GETBLOCKCOMMITMENT: return "getBlockCommitment";
  case KEYW_RPCMETHOD_GETBLOCKHEIGHT: return "getBlockHeight";
  case KEYW_RPCMETHOD_GETBLOCKPRODUCTION: return "getBlockProduction";
  case KEYW_RPCMETHOD_GETBLOCKS: return "getBlocks";
  case KEYW_RPCMETHOD_GETBLOCKSWITHLIMIT: return "getBlocksWithLimit";
  case KEYW_RPCMETHOD_GETBLOCKTIME: return "getBlockTime";
  case KEYW_RPCMETHOD_GETCLUSTERNODES: return "getClusterNodes";
  case KEYW_RPCMETHOD_GETCONFIRMEDBLOCK: return "getConfirmedBlock";
  case KEYW_RPCMETHOD_GETCONFIRMEDBLOCKS: return "getConfirmedBlocks";
  case KEYW_RPCMETHOD_GETCONFIRMEDBLOCKSWITHLIMIT: return "getConfirmedBlocksWithLimit";
  case KEYW_RPCMETHOD_GETCONFIRMEDSIGNATURESFORADDRESS2: return "getConfirmedSignaturesForAddress2";
  case KEYW_RPCMETHOD_GETCONFIRMEDTRANSACTION: return "getConfirmedTransaction";
  case KEYW_RPCMETHOD_GETEPOCHINFO: return "getEpochInfo";
  case KEYW_RPCMETHOD_GETEPOCHSCHEDULE: return "getEpochSchedule";
  case KEYW_RPCMETHOD_GETFEECALCULATORFORBLOCKHASH: return "getFeeCalculatorForBlockhash";
  case KEYW_RPCMETHOD_GETFEEFORMESSAGE: return "getFeeForMessage";
  case KEYW_RPCMETHOD_GETFEERATEGOVERNOR: return "getFeeRateGovernor";
  case KEYW_RPCMETHOD_GETFEES: return "getFees";
  case KEYW_RPCMETHOD_GETFIRSTAVAILABLEBLOCK: return "getFirstAvailableBlock";
  case KEYW_RPCMETHOD_GETGENESISHASH: return "getGenesisHash";
  case KEYW_RPCMETHOD_GETHEALTH: return "getHealth";
  case KEYW_RPCMETHOD_GETHIGHESTSNAPSHOTSLOT: return "getHighestSnapshotSlot";
  case KEYW_RPCMETHOD_GETIDENTITY: return "getIdentity";
  case KEYW_RPCMETHOD_GETINFLATIONGOVERNOR: return "getInflationGovernor";
  case KEYW_RPCMETHOD_GETINFLATIONRATE: return "getInflationRate";
  case KEYW_RPCMETHOD_GETINFLATIONREWARD: return "getInflationReward";
  case KEYW_RPCMETHOD_GETLARGESTACCOUNTS: return "getLargestAccounts";
  case KEYW_RPCMETHOD_GETLATESTBLOCKHASH: return "getLatestBlockhash";
  case KEYW_RPCMETHOD_GETLEADERSCHEDULE: return "getLeaderSchedule";
  case KEYW_RPCMETHOD_GETMAXRETRANSMITSLOT: return "getMaxRetransmitSlot";
  case KEYW_RPCMETHOD_GETMAXSHREDINSERTSLOT: return "getMaxShredInsertSlot";
  case KEYW_RPCMETHOD_GETMINIMUMBALANCEFORRENTEXEMPTION: return "getMinimumBalanceForRentExemption";
  case KEYW_RPCMETHOD_GETMULTIPLEACCOUNTS: return "getMultipleAccounts";
  case KEYW_RPCMETHOD_GETPROGRAMACCOUNTS: return "getProgramAccounts";
  case KEYW_RPCMETHOD_GETRECENTBLOCKHASH: return "getRecentBlockhash";
  case KEYW_RPCMETHOD_GETRECENTPERFORMANCESAMPLES: return "getRecentPerformanceSamples";
  case KEYW_RPCMETHOD_GETRECENTPRIORITIZATIONFEES: return "getRecentPrioritizationFees";
  case KEYW_RPCMETHOD_GETSIGNATURESFORADDRESS: return "getSignaturesForAddress";
  case KEYW_RPCMETHOD_GETSIGNATURESTATUSES: return "getSignatureStatuses";
  case KEYW_RPCMETHOD_GETSLOT: return "getSlot";
  case KEYW_RPCMETHOD_GETSLOTLEADER: return "getSlotLeader";
  case KEYW_RPCMETHOD_GETSLOTLEADERS: return "getSlotLeaders";
  case KEYW_RPCMETHOD_GETSNAPSHOTSLOT: return "getSnapshotSlot";
  case KEYW_RPCMETHOD_GETSTAKEACTIVATION: return "getStakeActivation";
  case KEYW_RPCMETHOD_GETSTAKEMINIMUMDELEGATION: return "getStakeMinimumDelegation";
  case KEYW_RPCMETHOD_GETSUPPLY: return "getSupply";
  case KEYW_RPCMETHOD_GETTOKENACCOUNTBALANCE: return "getTokenAccountBalance";
  case KEYW_RPCMETHOD_GETTOKENACCOUNTSBYDELEGATE: return "getTokenAccountsByDelegate";
  case KEYW_RPCMETHOD_GETTOKENACCOUNTSBYOWNER: return "getTokenAccountsByOwner";
  case KEYW_RPCMETHOD_GETTOKENLARGESTACCOUNTS: return "getTokenLargestAccounts";
  case KEYW_RPCMETHOD_GETTOKENSUPPLY: return "getTokenSupply";
  case KEYW_RPCMETHOD_GETTRANSACTION: return "getTransaction";
  case KEYW_RPCMETHOD_GETTRANSACTIONCOUNT: return "getTransactionCount";
  case KEYW_RPCMETHOD_GETVERSION: return "getVersion";
  case KEYW_RPCMETHOD_GETVOTEACCOUNTS: return "getVoteAccounts";
  case KEYW_RPCMETHOD_ISBLOCKHASHVALID: return "isBlockhashValid";
  case KEYW_RPCMETHOD_MINIMUMLEDGERSLOT: return "minimumLedgerSlot";
  case KEYW_RPCMETHOD_REQUESTAIRDROP: return "requestAirdrop";
  case KEYW_RPCMETHOD_SENDTRANSACTION: return "sendTransaction";
  case KEYW_RPCMETHOD_SIMULATETRANSACTION: return "simulateTransaction";
  case KEYW_WS_METHOD_ACCOUNTSUBSCRIBE: return "accountSubscribe";
  case KEYW_WS_METHOD_ACCOUNTUNSUBSCRIBE: return "accountUnsubscribe";
  case KEYW_WS_METHOD_BLOCKSUBSCRIBE: return "blockSubscribe";
  case KEYW_WS_METHOD_BLOCKUNSUBSCRIBE: return "blockUnsubscribe";
  case KEYW_WS_METHOD_LOGSSUBSCRIBE: return "logsSubscribe";
  case KEYW_WS_METHOD_LOGSUNSUBSCRIBE: return "logsUnsubscribe";
  case KEYW_WS_METHOD_PROGRAMSUBSCRIBE: return "programSubscribe";
  case KEYW_WS_METHOD_PROGRAMUNSUBSCRIBE: return "programUnsubscribe";
  case KEYW_WS_METHOD_ROOTSUBSCRIBE: return "rootSubscribe";
  case KEYW_WS_METHOD_ROOTUNSUBSCRIBE: return "rootUnsubscribe";
  case KEYW_WS_METHOD_SIGNATURESUBSCRIBE: return "signatureSubscribe";
  case KEYW_WS_METHOD_SIGNATUREUNSUBSCRIBE: return "signatureUnsubscribe";
  case KEYW_WS_METHOD_SLOTSUBSCRIBE: return "slotSubscribe";
  case KEYW_WS_METHOD_SLOTUNSUBSCRIBE: return "slotUnsubscribe";
  case KEYW_WS_METHOD_SLOTSUPDATESSUBSCRIBE: return "slotsUpdatesSubscribe";
  case KEYW_WS_METHOD_SLOTSUPDATESUNSUBSCRIBE: return "slotsUpdatesUnsubscribe";
  case KEYW_WS_METHOD_VOTESUBSCRIBE: return "voteSubscribe";
  case KEYW_WS_METHOD_VOTEUNSUBSCRIBE: return "voteUnsubscribe";
  case KEYW_JSON_EXCLUDENONCIRCULATINGACCOUNTSLIST: return "excludeNonCirculatingAccountsList";
  }
  return "???";
}
