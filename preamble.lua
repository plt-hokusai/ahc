local A, F, I = {}, {}, {}

local stack = {}
local sp = 1

local function repr(x)
  if type(x) == 'table' then
    if x[1] == F then
      return x[4]
    elseif x[1] == A then
      return repr(x[2]) .. '(' .. repr(x[3]) .. ')'
    elseif x[1] == I then
      return '&' .. repr(x[2])
    end
  else
    return tostring(x)
  end
end

local function unwind()
  local x = stack[sp]
  if type(x) == 'table' then
    if x[1] == A then
      stack[sp + 1] = x[2]; sp = sp + 1
      return unwind()
    elseif x[1] == I then
      stack[sp] = x[2]
      return unwind()
    elseif x[1] == F then
      if sp - 1 >= x[3] then
        return x[2]()
      else
        print("insufficient arguments for supercombinator " .. x[4])
        print 'stack dump:'
        for k, v in pairs(stack) do
          print(sp - k, repr(v))
        end
        error()
      end
    end
  else
    os.exit(x)
  end
end

local function getchar()
  local k = stack[sp - 1][3]; sp = sp - 1
  local knil = stack[sp - 1][3]; sp = sp - 1
  local ch = io.read(1)
  if ch then
    stack[sp] = { A, k, ch:byte() }
  else
    stack[sp] = { A, knil, 0 }
  end
  return unwind()
end

local getchar_combinator = { F, getchar, 2 }

local function putchar()
  local ch = stack[sp - 1][3];
  local k = stack[sp - 2][3]; sp = sp - 1
  io.write(string.char(ch))
  stack[sp] = { A, k, ch }
  return unwind()
end

local putchar_combinator = { F, putchar, 2 }
