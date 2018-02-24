/*@ requires \length(a) == 7;
    ensures  \is_pstring(\result, 6) && \prefix(\string(\result, 6), 3)== \suffix(\string(\result, 6), 3);
*/
char* strtest(char* a){
    a[0] = 'a'; a[1] = 'b'; a[2] = 'c'; a[3] = 'a'; a[4] = 'b'; a[5] = 'c'; a[6] = '\0';
    return a;
}


