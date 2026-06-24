(* MID_EXIT_CASE4: all 4 sub-iters of the i=N-1 block run clean (niblen stays <=248 through
   16i+4,16i+8,16i+12), loop back to pc+56 at pos16(i+1), where head-guard1 (cmp eax,248) fires
   TAKEN since niblen(16(i+1))>248 -> pc+318 at pos16(i+1).
   = CLEAN_BLOCK@i (pc+56/pos16i -> pc+56/pos16(i+1)) THEN head-guard1 eax-TAKEN -> pc+318.
   Load after: CLEAN_BLOCK, .subiter_bridge_lemmas (JA_TAKEN_GT), .midexit_subiter1 (q-defs reused conceptually). *)

(* q56 at pos 16(i+1): CLEAN_BLOCK's postcondition. *)
let me4_q56 =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 56) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
       read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
       read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list)) /\
       read RCX s = word(16*(i+1)) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist))`;;

let me4_pre =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 56) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
       read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
       read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
       read RCX s = word(16*i) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist))`;;

let me4_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 318) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list)) /\
       read RCX s = word(16*(i+1)) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist))`;;

let me4_cframe =
  `MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
   MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes (res,1024)]`;;

let midexit4_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 407) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(i+1)) inlist):int16 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[me4_pre; me4_post; me4_cframe])));;

(* Wait: CLEAN_BLOCK needs niblen(16(i+1))<=248 to run clean, but case-4 has niblen(16(i+1))>248.
   That's CONTRADICTORY -> case-4 as stated is VACUOUS. The real case-4 is: niblen at 16i+4,16i+8,16i+12
   all <=248 (3 internal guards don't fire) but niblen(16(i+1)=16i+16)>248 (head-guard1 of NEXT iter fires).
   CLEAN_BLOCK requires niblen(16(i+1))<=248 so it does NOT apply. Need a CLEAN_BLOCK variant that runs the
   4 sub-iters but ONLY needs the 3 internal niblens<=248 (the 4th guard is the NEXT head, not in-block). *)
Printf.printf "MID_EXIT_CASE4: needs CLEAN_BLOCK-without-final-bound variant; see note.\n";;
