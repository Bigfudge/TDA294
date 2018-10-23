public class Drawing{

    private /*@ spec_public @*/ boolean[][] canvas;


    /*@ public invariant
      @ (\forall int i; 0 <= i && i < canvas.length; canvas[i].length == canvas.length);		
      @*/
    
    /*@ public invariant
      @ (\forall int i,j;
      @          0 < i && 0 < j && i < canvas.length-1 && j < canvas[0].length-1;
      @          canvas[i][j] ==> (canvas[i][j-1] && canvas[i][j+1] || canvas[i-1][j] && canvas[i+1][j]));		
      @*/
     
    
    /*@ public normal_behaviour
      @ requires true;
      @ ensures true;
      @*/
    public Drawing(){
	canvas = new boolean[10][10];
    }
    
    /*@ public normal_behaviour
      @ requires true;
      @ ensures true;
      @*/
    public void drawHorizontal(int height){
	int i = 0;
	while (i < canvas.length){
	    canvas[i][height] = true;
	    i++; 
	}
    }
    
    /*@ public normal_behaviour
      @ requires depth >= 0 && depth < canvas.length;
      @ ensures true;
      @*/
    public void drawVertical(int depth){
	int i = 0;
	/*@ loop_invariant
	  @ 0 <= i && i < canvas[depth].length
	  @        && (\forall int x; 0 <= x && x < i; canvas[depth][x] == true);
	  @ assignable canvas[depth][*];
	  @ decreasing (canvas[depth].length) - i;
	  @*/
	while(i < canvas[depth].length){		
	    canvas[depth][i] = true;
	    i++;
	}
    }
    
    
    /*@ public normal_behaviour
      @ requires 0 < canvas.length;
      @ ensures true;
      @*/
    public void drawMultiple(){
	drawVertical(0);
	drawHorizontal(0);
    }   

}
