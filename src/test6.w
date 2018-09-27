%/include wombat.wh

    `test = { case $:Nat of [
                { $ = 0; 100}
                { $-1 }
              ]
            };
    print (test 4);
    6 = test `x; print x;
    print (test 0);
    100 = test `y; print y
