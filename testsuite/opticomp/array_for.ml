let () =
  let a = Array.make 5 0 in
  for i = 0 to (Array.length a) - 1 do
    a.(i) <- (-1)
  done
