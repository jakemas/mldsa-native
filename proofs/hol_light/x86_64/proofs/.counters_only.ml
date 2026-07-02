  X86_STEPS_TAC EXEC (18--21) THEN
  (fun g -> (let oc=open_out "/tmp/cs_c1821.txt" in output_string oc "counters 18-21 done"; close_out oc); ALL_TAC g) THEN
