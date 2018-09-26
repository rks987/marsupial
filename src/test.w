%/include wombat.wh

    `fact = { case $:Nat of [
                { $ = 0; 1}
                { $ = `n; n*fact(n-1) >=? n } # n-1 fails if n==0, "<=?n" stops backward
              ]
            };
    #print (fact 4);
    6:Nat = fact `x; print x

