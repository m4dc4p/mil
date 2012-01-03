outputtemplate := "%j-%c.svg";
outputformat := "svg";

% x & y represent the top of the diamon.
% The diamond is 1 unit tall and 1 unit wide.
def diamond(expr w, h, x, y, color, amt) =
  path p;
  p = (w*x, h*y){down} .. tension 2.5 .. {left}(w*(x-(amt*.5)), h*(y-(amt*.5))){right} .. tension 3 .. 
    {down}(w*x, h*(y - amt)){up} .. tension 2.5 ..
    {right}(w*(x+(amt*.5)), h*(y-(amt*.5))){left} .. tension 3 .. {up}cycle;
  fill p withcolor color;
enddef;

beginfig(1);
  scale=16; grid=8; debug = 0;
  defaultscale := 1.25 * scale;
  h=scale*3cm; w=scale*2cm; 
  incrw = w / grid; incrh = h / grid;
  draw (0,0) -- (0,h) -- (w,h) -- (w,0) -- (0,0);
  pickup pencircle scaled 4pt;

  if debug = 1:
    for i=0 upto grid:
      for j=0 upto grid:
        if i = 0: 
          if j = 0: dotlabel.urt(decimal(i) & ", " & decimal(j), (incrw*i ,incrh*j)); 
          elseif j = grid: dotlabel.lrt(decimal(i) & ", " & decimal(j), (incrw*i ,incrh*j)); 
          else: dotlabel.rt(decimal(i) & ", " & decimal(j), (incrw*i,incrh*j)); 
          fi 
        elseif i = grid:
          if j = 0: dotlabel.ulft(decimal(i) & ", " & decimal(j), (incrw*i,incrh*j)); 
          elseif j = grid: dotlabel.llft(decimal(i) & ", " & decimal(j), (incrw*i,incrh*j)); 
          else: dotlabel.lft(decimal(i) & ", " & decimal(j), (incrw*i,incrh*j)); 
          fi
        else: 
          if j = 0: dotlabel.top(decimal(i) & ", " & decimal(j), (incrw*i,incrh*j)); 
          elseif j = grid: dotlabel.bot(decimal(i) & ", " & decimal(j), (incrw*i,incrh*j)); 
          else: dotlabel.rt(decimal(i) & ", " & decimal(j), (incrw*i,incrh*j)); 
          fi
        fi
      endfor
    endfor
  fi
  drawoptions(withcolor red);
  picture num;
  num = image(label("4", (0,0)));
  draw num shifted (incrw*0.5, incrh*7.5);
  draw num reflectedabout ((0,0),(1,0))
      reflectedabout ((0,0),(0,1))
      shifted(incrw*7.5, incrh*.5);

  diamond(incrw, incrh, 1.5, 7.5, red, 1);
  diamond(incrw, incrh, 6.5, 7.5, red, 1);
  diamond(incrw, incrh, 1.5, 1.5, red, 1);
  diamond(incrw, incrh, 6.5, 1.5, red, 1);
  diamond(incrw, incrh, 0.5, 7, red, 0.5);
  diamond(incrw, incrh, 7.5, 1.5, red, 0.5);
endfig;


end;