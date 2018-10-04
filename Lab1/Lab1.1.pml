#define NUM_PHIL 4

int availableForks[NUM_PHIL] = 1
int numberOfForks = NUM_PHIL


proctype phil(int id) {
    //-1 indicates empty hands, otherwise contains forks
    int leftHand = -1;
    int rightHand = -1;
    
    int index;
    
    //Philosopher starts of not hungry
    bool hungry = false;
    
  do
    //Philosopher is thinking if not hungry
    :: hungry != true -->
        printf("Philosopher %u thinking\n", id);
        hungry = true;

       
    //Philosopher eats if both hands contains forks
    :: (leftHand != -1) && (rightHand != -1) && hungry -->
       printf("Philosopher %u is eating with fork %u and %u \n",id , leftHand, rightHand);
       atomic{
           availableForks[leftHand]=1;
           availableForks[rightHand]=1;
       }
       //Returns both forks
       leftHand=-1;
       rightHand=-1;
       hungry=false;

    
    //Looking for a available Fork
    ::((leftHand == -1) || (rightHand == -1)) && hungry -->
        for(index : 0 .. (numberOfForks-1)){
            atomic{
                do
                    :: availableForks[index] == 1 -->          
                        printf("Philosopher %u is taking fork %u \n",id, index);
                        availableForks[index]=0;
                        
                        //Calculates the number of remaining forks
                        int remainingForks = 0;
                        int i =0;
                        for(i in availableForks){
                            remainingForks = remainingForks+availableForks[i];
                        };
                        //printf("remainingforks %u \n",remainingForks);
                        do
                            //If the last fork was taken and the one hand is still empty the fork is returned.
                            ::(leftHand == -1) && (rightHand == -1) && (remainingForks == 0) -->
                                availableForks[index]=1;
                                index = numberOfForks;
                                printf("Putting back fork\n")
                                do
                                    //Put fork in the left hand if free
                                    ::(leftHand == -1) -->
                                        leftHand = index;
                                        index =numberOfForks;
                                        break;
                                    //Put fork in right hand if free
                                    ::(rightHand == -1) -->
                                        rightHand = index;
                                        index =numberOfForks;
                                        break;
                                    :: else-->
                                        index =numberOfForks;
                                        break;
                                od
                                break;  
                            :: else --> break
                        od;
                        break;
                    :: else --> break
                    
                od;
                //printf("hej2")
            };
        };
  od
}

init  {
  int i = 0;

  do
  :: i >= NUM_PHIL -> break
  :: else -> run phil(i);
         i++
  od
}