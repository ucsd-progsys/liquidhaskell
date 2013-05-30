
var Range = require("ace/range").Range;

/***********************************************************************/
/** Language Dependent *************************************************/
/***********************************************************************/

var splitters = [ ' ', '\t', '\n', '(' , ')', '[', ']' ];

/*@ isSplit :: (char) => boolean */
function isSplit(c){ 
  return (splitters.indexOf(c) >= 0); 
}

/***********************************************************************/
/** Shuffle the Cursor To Get to WordStart *****************************/
/***********************************************************************/

function wordRangeLo(s, col){
  if (isSplit(s[col])){
    return col;
  }

  var lo = col;
  
  while (0 < lo) {
    if (isSplit(s[lo - 1])){
      return lo;
    };
    lo = lo - 1;
  }
  return lo;
}

function wordRangeHi(s, col){
  
  if (isSplit(s[col])){
    return col;
  }

  var hi = col;
  
  while (hi < s.length - 1) {
    if (isSplit(s[hi + 1])) {
      return hi;
    }
    hi = hi + 1;
  }
  return hi;
}
  
 
/*@ localWordRange :: (string, int, int) => Range */
function localWordRange(str, row, col){
  var lo = wordRangeLo(str, col);
  var hi = wordRangeHi(str, col);
  var w  = str.slice(lo, 1 + hi);
  var r  = new Range(row, lo, row, 1 + hi);
  return r;
}

//////////////////////////////////////////////////////////////////////////////////////
// A simple box that follows the mouse around ////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////

var tooltipNode;

var TokenTooltip = function(editor, annotFun) {
    if (editor.tokenTooltip) return;
    editor.tokenTooltip = this;    
    
    this.editor   = editor;
    this.annotFun = annotFun;

    editor.tooltip = tooltipNode || this.$init();

    this.update = this.update.bind(this);
    this.onMouseMove = this.onMouseMove.bind(this);
    this.onMouseOut = this.onMouseOut.bind(this);

    editor.container.addEventListener("mousemove", this.onMouseMove, true);
    editor.container.addEventListener("mouseout", this.onMouseOut, true);

    // ORIG editor.on("mousemove", this.onMouseMove);
    // ORIG editor.on("mouseout",  this.onMouseOut);
    // ORIG event.addListener(editor.renderer.scroller, "mousemove", this.onMouseMove);
    // ORIG event.addListener(editor.renderer.content, "mouseout", this.onMouseOut);
};

(function(){
    this.token = {};
    // this.range = new Range();
    
    this.update = function() {
        this.$timer = null;
        
        var r = this.editor.renderer;
        if (this.lastT - (r.timeStamp || 0) > 1000) {
            r.rect = null;
            r.timeStamp = this.lastT;
            this.maxHeight = innerHeight;
            this.maxWidth = innerWidth;
        }

        var canvasPos = r.rect || (r.rect = r.scroller.getBoundingClientRect());
        var offset = (this.x + r.scrollLeft - canvasPos.left - r.$padding) / r.characterWidth;
        var row = Math.floor((this.y + r.scrollTop - canvasPos.top) / r.lineHeight);
        var col = Math.round(offset);

        var screenPos = {row: row, column: col, side: offset - col > 0 ? 1 : -1};
        var session = this.editor.session;
        var docPos = session.screenToDocumentPosition(screenPos.row, screenPos.column);
        
        var token = session.getTokenAt(docPos.row, docPos.column);

        if (!token && !session.getLine(docPos.row)) {
            token = {
                type: "",
                value: "",
                state: session.bgTokenizer.getState(0)
            };
        }
        if (!token) {
            session.removeMarker(this.marker);
            tooltipNode.style.display = "none";
            this.isOpen = false;
            return;
        }
        if (!this.isOpen) {
            tooltipNode.style.display = "";
            this.isOpen = true;
        }
        
        // ORIG var tokenText = token.type;
        // ORIG if (token.state)
        // ORIG     tokenText += "|" + token.state;
        // ORIG if (token.merge)
        // ORIG     tokenText += "\n  merge";
        // ORIG if (token.stateTransitions)
        // ORIG     tokenText += "\n  " + token.stateTransitions.join("\n  ");
        
        // ORIG var tokenText = "(" + docPos.row + ", " + docPos.column + ")";
        // ORIG var tokenText = this.annotFun(docPos.row, docPos.column); 
        // ORIG var tokRange  = session.getAWordRange(docPos.row, docPos.column);

        var line      = session.getLine(docPos.row);
        var tokRange  = localWordRange(line, docPos.row, docPos.column);  
        var tokenText = this.annotFun(tokRange.start.row, tokRange.start.column);

        // If there is no text, then go home.
        if (!tokenText) {
            session.removeMarker(this.marker);
            tooltipNode.style.display = "none";
            this.isOpen = false;
            return;
        }
        
        if (this.tokenText != tokenText) {
            tooltipNode.textContent = tokenText;
            this.tooltipWidth = tooltipNode.offsetWidth;
            this.tooltipHeight = tooltipNode.offsetHeight;
            this.tokenText = tokenText;
        }
        
        this.updateTooltipPosition(this.x, this.y);

        this.token = token;
        this.range = tokRange;
        session.removeMarker(this.marker);
        // ORIG this.range = this.editor.getSelectionRange();
        // ORIG this.range = new Range(docPos.row, token.start, docPos.row, token.start + token.value.length);
        this.marker = session.addMarker(this.range, "ace_bracket", "text");
    };
    
    this.onMouseMove = function(e) {
        this.x = e.clientX;
        this.y = e.clientY;
        if (this.isOpen) {
            this.lastT = e.timeStamp;
            this.updateTooltipPosition(this.x, this.y);
        }
        if (!this.$timer)
            this.$timer = setTimeout(this.update, 50);
    };
    
    this.onMouseOut = function(e) {
        var t = e && e.relatedTarget;
        var ct = e &&  e.currentTarget;
        while(t && (t = t.parentNode)) {
            if (t == ct)
                return;
        }
        tooltipNode.style.display = "none";
        this.editor.session.removeMarker(this.marker);
        this.$timer = clearTimeout(this.$timer);
        this.isOpen = false;
    };
    
    this.updateTooltipPosition = function(x, y) {
        var st = tooltipNode.style;
        if (x + 10 + this.tooltipWidth > this.maxWidth)
            x = innerWidth - this.tooltipWidth - 10;
        if (y > innerHeight * 0.75 || y + 20 + this.tooltipHeight > this.maxHeight)
            y = y - this.tooltipHeight - 30;
        
        st.left = x + 10 + "px";
        st.top = y + 20 + "px";
    };

    this.$init = function() {
        var ttDiv   = document.createElement("div");
        tooltipNode = document.documentElement.appendChild(ttDiv);
        ttDiv.className = "typeToolTip";

        var st = tooltipNode.style;
        st.display = "none";
        // st.position = "fixed";
        // st.background = "lightyellow";
        // st.borderRadius = "5px";
        // st.border = "1px solid gray";
        // st.padding = "1px";
        // st.zIndex = 1000;
        // st.fontFamily = "monospace";
        // st.whiteSpace = "pre";
        return tooltipNode;
    };

    this.destroy = function() {
        this.onMouseOut();
        // event.removeListener(this.editor.renderer.scroller, "mousemove", this.onMouseMove);
        // event.removeListener(this.editor.renderer.content, "mouseout", this.onMouseOut);
        delete this.editor.tokenTooltip;    
    };

}).call(TokenTooltip.prototype);

