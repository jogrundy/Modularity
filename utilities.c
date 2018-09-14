//
//  utilities.c
//  expt1
//
//  Created by Joanna Houghton on 07/08/2018.
//  Copyright © 2018 JoSoft. All rights reserved.
//

#include "utilities.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

void printIntArr(int *arr, int len){
    int i;
    printf("printing integer array..\n");
    for (i=0;i<len;i++) {
        printf("%d\n", arr[i]);
    }
}
void printDoubleArr(double *arr, int len){
    int i;
    printf("printing double array..\n");
    for (i=0;i<len;i++) {
        printf("%.3f\n", arr[i]);
    }
}

void printfDoubleArr(FILE *f, int t, double *arr, int len){
    int i;
    fprintf(f, "%i", t);
    for (i=0;i<len;i++) {
        fprintf(f, ", %0.3f", arr[i]);
    }
    fprintf(f, "\n");
}

void shuffle_d(double *arr, int t){
    // t is length of arr to be shuffled in place
    //    srand48(time(NULL));
    int j = t-1;
    while (j>=1){
        double U = drand48();
        int k = ceil(j*U)-1;
        // exchange arr[k] wtih arr[j]
        double tmp = arr[k];
        arr[k] = arr[j];
        arr[j] = tmp;
        //        printIntArr(arr, t);
        j -=1;
    }
}

void shuffle_i(int *arr, int t){
    // t is length of arr to be shuffled in place
    //    srand48(time(NULL));
    int j = t-1;
    while (j>=1){
        double U = drand48();
        int k = ceil(j*U)-1;
        // exchange arr[k] wtih arr[j]
        int tmp = arr[k];
        arr[k] = arr[j];
        arr[j] = tmp;
        //        printIntArr(arr, t);
        j -=1;
    }
}

double rand_gauss(double mean, double sd){
    //    from numerical recipes in C, pg 289 - Box Muller algorithm
    //    using drand48() as supply of uniform dist nos.
    //    correcting for mean and sd
    //    srand48(time(NULL));
    double v1, v2, fac, rsq, res;
    do{
        v1 = 2.0*drand48()-1.0;
        v2 = 2.0*drand48()-1.0;
        rsq = v1*v1 + v2*v2;
        
    } while (rsq >=1 || rsq == 0); // only allows numbers inside the circle
    
    fac = sqrt(-2 * log(rsq)/rsq);
    res = v1*fac;
    return (res * sd)+mean;
}

void count_arr(int *count, int len){
    //    gives count from zero to len-1
    int i;
    for (i=0;i<len;i++){
        count[i]=i;
    }
}

int argmax(double *arr, const int n){
    //    does arg max to ensure i get the highest eigenvalue and the corresponding eigenvector, returns index of max element, the first of that same size if more than one
    int i, max_ind=-1;
    double max = -1;
    for (i=0;i<n;i++){
        if (arr[i]>max){
            max = arr[i];
            max_ind = i;
        }
    }
    return max_ind;
}

bool is_in(int *array, int query, int len){
    // checks for membership of array
    int i;
    for (i=0;i<len;i++){
        if (array[i] == query){
            return true;
            
        }
    }
    return false;
}

double array_mean(double *array, int len){
    int i;
    double arr_sum = 0;
    for (i=0;i<len;i++){
        arr_sum +=array[i];
    }
    return arr_sum/(double)len;
}

double array_stddev(double *array, int len){
    double mu = array_mean(array, len);
    int i;
    double arr_dev_sum = 0;
    for (i=0;i<len;i++){
        arr_dev_sum +=(array[i] - mu)*(array[i] - mu);
    }
    double var =  arr_dev_sum/(double)(len);
    return sqrt(var);
}


int arr_row_sum(int *arr, int row_start, int row_end){
    int i, sum=0;
    for (i=0;i<row_end;i++){
        sum += arr[i];
    }
    return sum;
}

int arr_col_sum(int *arr, int col_start, const int size, int n){
    int i, sum=0;
    for (i=0;i<size;i++){
        if (i % n == col_start){
            sum += arr[i];
        }
        
    }
    return sum;
}



double std_dev(double *arr, const int size)
{
    double mu, std_dev = 0.0;
    int i;
    mu = mean(arr, size);
    for(i=0;i<size;i++) {
        std_dev += (arr[i] - mu)*(arr[i]-mu);
    }
    return sqrt(std_dev/size);
}
double mean(double *arr, const int size)
{
    double sum = 0.0;
    int i;
    for(i=0;i<size;i++){
        sum += arr[i];
    }
    return sum/size;
}
double sum_double_array(double *arr, int n){
    int i;
    double total = 0;
    for (i=0;i<n;i++){
        total += arr[i];
    }
    return total;
}

double sum_int_array(int *arr, int n){
    int i;
    double total = 0;
    for (i=0;i<n;i++){
        total += arr[i];
    }
    return total;
}

void test_rng(double mu, double sigma){
    //    tests rng generator by outputting numbers to text file, python plots histogram alongside its own
    FILE *f;
    //    char str[N];
    char* filename = "/Users/Jojo/MSc Stuff/Project/code/rng_test.txt";
    f = fopen(filename, "w");
    if (f == NULL){
        printf("could not open file %s\n", filename);
        exit(1);
    }
    int n = 1000;
    int i;
    for (i=0;i<n;i++){
        double num = rand_gauss(mu, sigma);
        fprintf(f, "%0.3f\n", num);
//        printf("%0.3f\n", num);
    }
    fclose(f);
}

double total_absolute_weight_array(double *array, int len){
    double abs_sum = 0;
    int i;
    for (i=0;i<len;i++){
        abs_sum += fabs(array[i]);
    }
    return abs_sum;
}
void invert_all_elements(double *array, int len, double *inv_array){
    // returns 1/each element
    int i;
    for (i=0;i<len;i++){
        if (fabs(array[i])>0){
            inv_array[i] = fabs((double )1/array[i]);
        } else {
            inv_array[i]=0;
        }
    }
}

void multiply_all_elements_d(double *input_array, int len, double *result_array, double multiplier){
    // multiplies every element of input_array by divisor and puts result in result_array
    int i;
    for (i=0;i<len;i++){
        result_array[i] = input_array[i]*multiplier;
    }
}

void multiply_all_elements_i(int *input_array, int len, double *result_array, double multiplier){
    // multiplies every element of input_array by divisor and puts result in result_array
    int i;
    for (i=0;i<len;i++){
        result_array[i] = input_array[i]*multiplier;
    }
}

double chi_squared_norm(double *array, int len){ // using normalised frequencies

    double expected =1.0/(double )len;
    int i;
    double chi_squared_sum=0;
    for (i=0;i<len;i++) {
        double chi = (array[i]-expected)*(array[i]-expected)/expected;
        chi_squared_sum +=chi;
    }
    return chi_squared_sum;
}

double chi_squared_count(int *array, int len){ // using counts
    double total = sum_int_array(array, len); // gives total number of observations
    double norm_array[len];

    multiply_all_elements_i(array, len, norm_array, 1.0/(double)total);
    double expected =total/(len*total);
    int i;
    double chi_squared_sum=0;
    for (i=0;i<len;i++) {
        double chi = (norm_array[i]-expected)*(norm_array[i]-expected)/expected;
        chi_squared_sum +=chi;
    }
    return chi_squared_sum;
}

void test_utilities(){
    // not testing print to file functions
    
    // test print int array:
    printf("testing print int array\n");
    printf("should have:\n");
    printf("1\n2\n3\n4\n");
    int arr[4] = {1,2,3,4};
    printIntArr(arr, 4);
    
    // test print double array
    printf("testing print int array\n");
    printf("should have:\n");
    printf("1.000\n2.000\n3.000\n4.000\n");
    double arr_d[4] = {1,2,3,4};
    printDoubleArr(arr_d, 4);
    
    // test shuffle_d
    printf("testing shuffle double array\n");
    double arr_d2[5] = {1,2,3,4,5};
    printf("unshuffled..\n");
    printDoubleArr(arr_d2, 5);
    shuffle_d(arr_d2, 5);
    printf("shuffled..\n");
    printDoubleArr(arr_d2, 5);
    
    // test shuffle_i
    printf("testing shuffle int array\n");
    int arr_i2[5] = {1,2,3,4,5};
    printf("unshuffled..\n");
    printIntArr(arr_i2, 5);
    shuffle_i(arr_i2, 5);
    printf("shuffled..\n");
    printIntArr(arr_i2, 5);
    
    // testing gaussian rng
    test_rng(0.5, 4);
    printf("testing gaussian rng, need to plot results in python to check\n");
    printf("results plotted in /code/rng_test.txt\n");
    // plot results in python to check accuracy
    
    // testing count arr
    printf("testing count_arr\n");
    printf("making array from 0 to 10..\n");
    int arr_i3[10]= {0,0,0,0,0,0,0,0,0,0};
    count_arr(arr_i3, 10);
    printIntArr(arr_i3, 10);
    
    //testing argmax
    printf("testing argmax for array..\n");
    double arr_d3[10] = {0,4,2,3,4,3.2,0.1,-7, -8.6, 2.1};
    printDoubleArr(arr_d3, 10);
    printf("arg max should return 1, does return %i\n", argmax(arr_d3, 10) );
    
    //testing is_in
    printf("testing is_in\n");
    printf("is 4 in array below?\n");
    printIntArr(arr_i2, 5);
    bool in = is_in(arr_i2, 4, 5);
    printf("Yes it should be true, is %i (0 is false, 1 is true)\n",in);
    
    printf("is 7 in array below?\n");
    printIntArr(arr_i2, 5);
    bool in_2 = is_in(arr_i2, 7, 5);
    printf("No it should be false, is %i (0 is false, 1 is true)\n",in_2);
    
    // testing array mean
    printf("testing array mean..\n");
    printf("mean of following array..\n");
    double arr_d4[10] = {0,1,2,3,4,3.2,0.1,-7, -8.6, 2.1};
    printDoubleArr(arr_d4, 10);
    printf("mean should be -0.020, is %0.03f\n", array_mean(arr_d4, 10));
    
    // testing array std dev
    printf("testing array std dev..\n");
    printf("std of previous array..\n");
    printf("std dev should be 4.094, is %0.03f\n", array_stddev(arr_d4, 10));
    
    
    
}
