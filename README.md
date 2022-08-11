# GNFS_SageMath
General Number Field Sieve Factoring Algorithm in SageMath

This is my implementation of the General Number Field Sieve (or GNFS) algorithm, which is the fastest known prime factorization algorithm on classical computers. 
https://en.wikipedia.org/wiki/General_number_field_sieve

The General Number Field Sieve algorithm has been used to factor RSA keys up to 512 bits long, and is the reason why you should never use RSA-512 (or RSA-1024 for that matter).
https://link.springer.com/content/pdf/10.1007/3-540-45539-6_1.pdf

ACKNOWLEDGEMENTS:
In terms of calculating squares and square roots in Z[θ], I have relied on the code of Professor William Stein:
https://wstein.org/wiki/ant07(2f)projects(2f)shumow_raw.html </br>
https://wstein.org/misc/aly-lll/gnfs.html </br>
Worth noting that Stein did say that "In reality this would be done with the CRT." Using the Chinese Remainder Theorem to calculate square roots of polynomials might be implemented in a future version. 


There is a slight modification needed to make to Stein's code in order to make it work in the year 2022:
https://web.archive.org/web/20220724010535/https://groups.google.com/g/sage-support/c/LTQjSUDoT8Q

I have included a Jupyter notebook, and a .Sage file of the same code (if you want to run it in a sage shell for some reason). 
To run in a sage shell, run it like this:
````
load("GNFS_v1.0.sage")
````
I would recommend utilitzing the configuration file, and make any modifications to it that you wish. To comment out any lines in the configuration file, include a "#" as the first character. Make sure to avoid using spaces when possible in the configuration file (especially on either end of an equals "=" sign). 

The complete implementation is not yet done, there are a lot of features yet to add. 

![image](https://user-images.githubusercontent.com/61210670/182726245-0d45c1fe-166d-4350-804d-a70e06645b2b.png)

![image](https://user-images.githubusercontent.com/61210670/182726291-0d2db6a8-916f-40cf-a146-3c16ee025144.png)
