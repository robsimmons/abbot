structure Symbol :> SYMBOL = struct
  datatype t = Loop of t
end
