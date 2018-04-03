%/include wombat.wh

    `fact = { case $:Nat of [
                { $ = 0; 1}
                { $ = `n >? 0; n*fact(n-1)}
              ]
            };
    print (fact 4);
    6 = fact `x; print x
