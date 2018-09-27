%/include wombat.wh

    `fact = { case $:Nat of [
                { $ = 0; 1}
                { $ = `n; n*fact(n-1) >=? n }
              ]
            };
    print (fact 4)
#    6 = fact `x; print x

