%/include wombat.wh

    `fact = { case $:Nat of [
                { $ = 0; 1}
                { $ = `n; n*fact(n-1) } # n-1 fails if n==0
              ]
            };
    print (fact 4)

