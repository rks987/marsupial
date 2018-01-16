%/include wombat.wh
1 - 2 * 3
#[] [ () ] [() ()]

    `fact = { case $:Nat of [
                { $ = 0; 1}
                { $ = `n >? 0; n*fact(n-1)}
              ]
            };

    6 = fact `x; print x
