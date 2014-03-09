structure Analysis =
struct
  
   type ana = {
       sorts: string list list,
       issrt: string -> bool,
       symbs: string list,
       issym: string -> bool,
       opers: string -> string list,
       arity: string -> string -> (string list * string) list,
       binds: string -> string -> bool,
       mutual: string -> string list,
       mutualwith: string -> string -> bool
   }

   val godel: ana = {
       sorts = [["exp"], ["tp"]],
       issrt = (fn "exp" => true | "tp" => true | _ => false),
       symbs = [],
       issym = (fn _ => false),
       opers = (fn "exp" => ["Z", "S", "Rec", "Lam", "App"]
               | "tp" =>  ["Nat", "Arr"]
               | _ => raise Fail ""),
       arity = (fn "exp" => 
                 (fn "Z" => []
                 | "S" => [([], "exp")]
                 | "Rec" => [([], "exp"), ([], "exp"), (["exp", "exp"], "exp")]
                 | "Lam" => [([], "tp"), (["exp"], "exp")]
                 | "App" => [([], "exp"), ([], "exp")]
                 | _ => raise Fail "")
               | "tp" =>
                 (fn "Nat" => []
                 | "Arr" => []
                 | _ => raise Fail "")
               | _ => raise Fail ""),
       binds = (fn s => fn t => s = t),
       mutual = (fn s => [s]),
       mutualwith = (fn s => fn t => s = t)
   }

   val minalgol: ana = {
       sorts = [["tp"], ["exp", "cmd"]],
       issrt = (fn s => List.exists (List.exists (fn t => s = t)) 
                                     [["tp"], ["exp", "cmd"]]),
       symbs = ["assign"],
       issym = (fn "assign" => true | _ => false),
       opers = (fn "tp" => ["Nat"]
                | "exp" => ["Cmd", "Z"]
                | "cmd" => ["Bnd", "Ret", "Dcl", "Get"]
                | _ => raise Fail ""),
       arity = (fn "tp" => 
                 (fn "Nat" => [])
               | "exp" =>
                 (fn "Z" => []
                 | "Cmd" => [([], "cmd")])
               | "cmd" => 
                 (fn "Bnd" => [([], "exp"), (["exp"], "cmd")]
                 | "Ret" => [([], "exp")]
                 | "Dcl" => [([], "exp"), (["assign"], "cmd")]
                 | "Get" => [([], "assign")])
               | _ => raise Fail ""),
       binds = (fn "cmd" => 
                 (fn "exp" => true
                 | _ => false)
               | "exp" => 
                 (fn "exp" => true
                 | _ => false)
               | _ => (fn _ => false)), 
       mutual = (fn "exp" => ["exp", "cmd"]
                 | "cmd" => ["exp", "cmd"]
                 | s => [s]),
       mutualwith = (fn s =>
                        (fn "exp" => s = "exp" orelse s = "cmd"
                        | "cmd" => s = "exp" orelse s = "cmd"
                        | t => s = t))
   }
                    

       

(* val pcf_pattern = {
       typs = [["tp"], ["side"], ["pat"], ["exp", "rules", "rule"]],
       cons = (fn "tp" => ["nat", "parr", "unit", "pair", "zero", "sum"]
              | "pat" => ["wild", "var", "z", "s", "triv", "pair", "in"]
              | "exp" => ["fix", "z", "s", "ifz", "lam", "app",
                          "triv", "pair", "pr",
                          "abort", "in", "case", 
                          "match"]
              | "rules" => ["rules"]
              | "rule" => ["rule"]),
       (* arity = (fn "tp" =>
                   (fn "nat" =>
                   | "parr" =>
                   | "unit" =>
                   | "pair" =>
                   | "zero" =>
                   | "sum" => *)
   } *)

end
