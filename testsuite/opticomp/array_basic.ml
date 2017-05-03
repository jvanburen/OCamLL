let () =
  let a = Array.make 5 0 in
  let b = Array.length a - 1 in
  let () = if b < Array.length a then Array.set a 0 1 else () in
  ()
                       
