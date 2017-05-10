let f a =
  if 0 < Array.length a
    then Array.set a 0 1
    else ()
