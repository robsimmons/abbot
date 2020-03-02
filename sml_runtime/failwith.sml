structure Failwith = struct
fun failwith string = raise (Fail string)
end
