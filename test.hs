data List a = Nil | Cons a (List a);
map f xs = case xs of { Nil -> Nil; Cons x xs -> Cons (f x) (map f xs) };
readall k = getchar (\ch -> readall (\xs -> k (Cons ch xs))) (\ch -> k Nil);
putall x xs = case xs of { Nil -> x; Cons x xs -> putchar x (\ch -> putall x xs) };
id x = x;
main x = readall (putall x);
