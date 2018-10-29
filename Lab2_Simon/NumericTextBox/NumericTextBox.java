/*
 * This class represents a text box for numeric values.
 * Its content is represented as an array of single digits.
 *
 * Your task is to add JML contracts for each method in this class
 * that reflect the informal descriptions in the Javadoc comments.
 *
 * Also add JML invariants for the fields "cursorPosition" and "content" that make sure that
 *
 *  - the cursorPosition is always a valid value (see comment for cursorPosition).
 *  - the content before the cursor contains only single digits
 *  - the content after the cursor is EMPTY
 *
 * Furthermore, think about which methods are pure and use the appropriate annotation.
 *
 * Hint: If you use variables for array indices in an assignable-clause,
 *       their values are evaluated in the pre-state.
 */
public class NumericTextBox
{
    public final int EMPTY = -1;

    /**
	 * The current cursor position, i.e. the position after the previously entered digit.
	 * If this is 0, then the cursor is placed at the very beginning of the text box.
	 * Note that the number of possible cursor positions is greater by one than
	 * the length of the text box.
	 */
/*@
	 @public invariant(0 <= cursorPosition && cursorPosition <= content.length);

@*/
	private /*@ spec_public @*/ int cursorPosition;

	/**
	 * This array stores the contents of the text box. At every position
	 * before the cursor, there is a valid value (i.e. a single digit).
	 * Positions after the cursor must be EMPTY.
	 */


	 /*@
	 @public invariant content!=null;
	 @public invariant (\forall int i; 0 <=i && i < cursorPosition; isSingleDigit(content[i]));
	 @public invariant (\forall int i; i >= cursorPosition && i < content.length; content[i] == EMPTY);
	 @*/
	private /*@ spec_public @*/ int[] content;

	/**
	 * Holds the current TextBoxRenderer. This can be null, which means that there
	 * is no renderer assigned.
	 */
	private /*@ spec_public nullable @*/  TextBoxRenderer textBoxRenderer;

	/**
	 * Gets the currently assigned TextBoxRenderer.
	 */
	 /*@
	 	@requires(textBoxRenderer != null);
	 	@ensures(\result != null);
	 @*/
	public /*@ pure nullable @*/  TextBoxRenderer getRenderer()
	{
		return(this.textBoxRenderer);
	}

	/**
	 * Sets the TextBoxRenderer used for rendering this text box.
	 * It can also be set to null, if the text box is not rendered.
	 */

	 /*@
	 	@requires(renderer != null);
	 	@ensures(getRenderer() == renderer);
        @assignable textBoxRenderer;
	 @*/
	public/*@nullable@*/ void setRenderer(TextBoxRenderer renderer)
	{
		this.textBoxRenderer=renderer;
	}

	/**
	 * Checks whether a given input is a single digit (i.e. between 0 and 9).
	 *
	 * @param input The input character.
	 * @return true if the input is a single digit, false otherwise.
	 */
    /*@
    @public normal_behavior
    @requires(isSingleDigit(input));
    @ensures(\result == true);

    @also

    @public normal_behavior
    @requires !(isSingleDigit(input));
    @ensures(\result == false);
    @*/
	public /*@ pure @*/  boolean isSingleDigit(int input)
	{
		if (input >=0 && input <= 9) {
			return true;
		}
		return false;
	}

	/**
	 * Clears the text box and resets the cursor to the start.
	 * Also sets the contentChanged flag of the current TextBoxRenderer, if any.
	 */
	 /*@
	      @ public normal_behavior
	      @ ensures cursorPosition == 0;
	      @ ensures (\forall int i; i >= 0 && i < content.length; content[i] == EMPTY);
		   @ ensures (textBoxRenderer == null) || textBoxRenderer.contentChanged;
	      @ assignable textBoxRenderer.contentChanged, cursorPosition, content[*];
	      @
	      @also
	      @
	      @ public normal_behavior
	      @ requires (\exists int i; i >= 0 && i < content.length; content[i] != EMPTY);
		  @ ensures cursorPosition == 0;
	      @ ensures (\forall int i; i >= 0 && i < content.length; content[i] == EMPTY);
		  @ ensures (textBoxRenderer == null) || textBoxRenderer.contentChanged;
	      @ assignable textBoxRenderer.contentChanged, cursorPosition, content[*];
	      @*/
	public void clear()
	{
		/*@ loop_invariant
		  @ 0 <= i && i <= content.length
		  @        && (\forall int x; 0 <= x && x < i; content[x] == EMPTY);
		  @ assignable content[*];
		  @ decreasing content.length - i;
		  @*/
		for (int i=0; i < content.length; i++) {
				this.content[i]=EMPTY;
		}
		if (textBoxRenderer!=null) {
			textBoxRenderer.contentChanged=true;
		}
		cursorPosition=0;

	}

	/**
	 * Enters a given input character into the text box and moves the cursor forward.
	 * If the input can be processed, the contentChanged flag of the current TextBoxRenderer (if any) is set.
	 * If an exception occurs, the TextBoxRenderer's showError flag is set instead.
	 *
	 * @param input the input character.
	 *
	 * @throws IllegalArgumentException if the input was not a single digit.
	 *
	 * @throws RuntimeException if the input was valid, but the cursor is at the end
	 *                          of the text box and no further input can be accepted.
	 */
     /*@
     @public normal_behavior
     @requires(isSingleDigit(input)==true);
	 @requires(cursorPosition < content.length);
     @ensures(textBoxRenderer.contentChanged==true || textBoxRenderer==null);
     @ensures(cursorPosition == \old(cursorPosition+1));
     @ensures(content[\old(cursorPosition)]==input);
     @assignable textBoxRenderer.contentChanged,cursorPosition, content[*];

     @also

     @public exceptional_behavior
     @requires !isSingleDigit(input);
	 @signals_only IllegalArgumentException;
	 @signals (IllegalArgumentException)
	 	(textBoxRenderer.showError == true) | (textBoxRenderer == null);
	 @assignable textBoxRenderer.showError;

     @also

     @public exceptional_behavior
     @requires isSingleDigit(input);
     @requires cursorPosition>=content.length;
     @assignable textBoxRenderer.showError;
	 signals_only RuntimeException;
 	signals (RuntimeException) (textBoxRenderer.showError == true) | (textBoxRenderer == null);
 	assignable textBoxRenderer.showError;

     @*/
	public void enterCharacter(int input)
	{
		if (isSingleDigit(input) && cursorPosition < content.length && cursorPosition >= 0) {

			content[cursorPosition]=input;
			cursorPosition++;
			if(textBoxRenderer != null){
				textBoxRenderer.contentChanged=true;
			}
		}
		else if(!(input >=0 && input <=9)){
			if(textBoxRenderer != null){
				textBoxRenderer.showError=true;
			}
			throw new IllegalArgumentException();
		}
		else if (cursorPosition>=content.length) {
			if(textBoxRenderer != null){
				textBoxRenderer.showError=true;
			}
			throw new RuntimeException();
		}
	}

	/**
	 * Deletes the most recently entered character and moves the cursor back one position.
	 * Also sets the current TextBoxRenderer's contentChanged flag (if any).
	 *
	 * @throws RuntimeException if the cursor is at the very beginning. In this case
	 *                          the showError flag of the TextBoxRenderer is set
	 *                          before the exception is thrown.
	 */
     /*@
     @public normal_behavior
	 @requires cursorPosition >0;
     @ensures(cursorPosition== (\old(cursorPosition)-1));
     @ensures(content[cursorPosition]==EMPTY);
     @ensures(textBoxRenderer.contentChanged == true || textBoxRenderer==null);
     @assignable textBoxRenderer.contentChanged, cursorPosition, content[*];


     @also

     @public exceptional_behavior
     @requires(cursorPosition<=0);
     @assignable textBoxRenderer.showError;
	 @signals_only RuntimeException;
	 @signals (RuntimeException) (textBoxRenderer.showError == true) |
			 (textBoxRenderer == null);
     @*/
	public void backspace()
	{
		if (cursorPosition==0) {
			if(textBoxRenderer != null){
				textBoxRenderer.showError=true;
			}
			throw new RuntimeException();
		}

		else if(cursorPosition>0){
			cursorPosition--;
			content[cursorPosition]=EMPTY;
			if(textBoxRenderer != null){
				textBoxRenderer.contentChanged=true;
			}
		}

	}
}

/**
 * This class represents a renderer that is responsible for displaying the
 * text box to the user in some way.
 */
class TextBoxRenderer
{
	/**
	 * Whether the content was changed (so the rendered text box needs a refresh).
	 */
	public boolean contentChanged = false;

	/**
	 * Whether an exception occured (which should be represented in the rendered text box).
	 */
	public boolean showError = false;
}
