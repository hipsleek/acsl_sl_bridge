(* Plugin registration and command-line options for the SL bridge. *)

include Plugin.Register (struct
  let name = "SL"
  let shortname = "sl"
  let help =
    "Parse separation-logic annotations (/*@[SL] ... */) and attach them \
     to functions as ACSL contracts"
end)

module Enabled = False (struct
  let option_name = "-sl"
  let help = "Translate /*@[SL] ... */ blocks into ACSL function contracts"
end)

module Show = False (struct
  let option_name = "-sl-show"
  let help = "Print each SL block next to its translated ACSL contract"
end)

(* The kernel's ACSL parser chokes on the "/*@[SL] ... */" marker (the '[' token)
   and, by default, treats that as a fatal error. When -sl is enabled we silence
   that category: the plugin recovers the SL by re-reading the raw source, so the
   kernel is expected to skip these comments. Runs at option-set time, before the
   AST is built. *)
let () =
  Enabled.add_set_hook (fun _ enabled ->
      if enabled then
        Kernel.set_warn_status Kernel.wkey_annot_error Log.Winactive)
