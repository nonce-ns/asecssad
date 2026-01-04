local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 212) then
					if (Enum <= 105) then
						if (Enum <= 52) then
							if (Enum <= 25) then
								if (Enum <= 12) then
									if (Enum <= 5) then
										if (Enum <= 2) then
											if (Enum <= 0) then
												local A;
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												if (Stk[Inst[2]] <= Stk[Inst[4]]) then
													VIP = VIP + 1;
												else
													VIP = Inst[3];
												end
											elseif (Enum > 1) then
												local A;
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												if not Stk[Inst[2]] then
													VIP = VIP + 1;
												else
													VIP = Inst[3];
												end
											else
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = #Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											end
										elseif (Enum <= 3) then
											local A = Inst[2];
											Stk[A] = Stk[A]();
										elseif (Enum > 4) then
											local A = Inst[2];
											local T = Stk[A];
											local B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										else
											local K;
											local B;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum <= 8) then
										if (Enum <= 6) then
											local B;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Enum == 7) then
											local B;
											local A;
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 10) then
										if (Enum == 9) then
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
										else
											local A;
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
										end
									elseif (Enum == 11) then
										local A;
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum <= 18) then
									if (Enum <= 15) then
										if (Enum <= 13) then
											local B;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Enum == 14) then
											local Results;
											local Edx;
											local Results, Limit;
											local B;
											local A;
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results, Limit = _R(Stk[A](Stk[A + 1]));
											Top = (Limit + A) - 1;
											Edx = 0;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results = {Stk[A](Unpack(Stk, A + 1, Top))};
											Edx = 0;
											for Idx = A, Inst[4] do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										else
											local B;
											local A;
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										end
									elseif (Enum <= 16) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 17) then
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									else
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 21) then
									if (Enum <= 19) then
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									elseif (Enum > 20) then
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 23) then
									if (Enum > 22) then
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum == 24) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 38) then
								if (Enum <= 31) then
									if (Enum <= 28) then
										if (Enum <= 26) then
											local Edx;
											local Results;
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results = {Stk[A](Stk[A + 1])};
											Edx = 0;
											for Idx = A, Inst[4] do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										elseif (Enum > 27) then
											local A = Inst[2];
											local Results = {Stk[A](Stk[A + 1])};
											local Edx = 0;
											for Idx = A, Inst[4] do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
										else
											local K;
											local B;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 29) then
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									elseif (Enum == 30) then
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 34) then
									if (Enum <= 32) then
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 33) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 36) then
									if (Enum > 35) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local A = Inst[2];
										local Step = Stk[A + 2];
										local Index = Stk[A] + Step;
										Stk[A] = Index;
										if (Step > 0) then
											if (Index <= Stk[A + 1]) then
												VIP = Inst[3];
												Stk[A + 3] = Index;
											end
										elseif (Index >= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									end
								elseif (Enum == 37) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 45) then
								if (Enum <= 41) then
									if (Enum <= 39) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									elseif (Enum > 40) then
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									else
										local Edx;
										local Results;
										local A;
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 43) then
									if (Enum > 42) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									end
								elseif (Enum > 44) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum <= 48) then
								if (Enum <= 46) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 47) then
									local T;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 50) then
								if (Enum == 49) then
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum > 51) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 78) then
							if (Enum <= 65) then
								if (Enum <= 58) then
									if (Enum <= 55) then
										if (Enum <= 53) then
											local Edx;
											local Results, Limit;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results, Limit = _R(Stk[A](Stk[A + 1]));
											Top = (Limit + A) - 1;
											Edx = 0;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Top));
										elseif (Enum == 54) then
											local K;
											local B;
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
										else
											local Edx;
											local Results;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results = {Stk[A](Stk[A + 1])};
											Edx = 0;
											for Idx = A, Inst[4] do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										end
									elseif (Enum <= 56) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 57) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 61) then
									if (Enum <= 59) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									elseif (Enum > 60) then
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local A;
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 63) then
									if (Enum > 62) then
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									else
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum > 64) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 71) then
								if (Enum <= 68) then
									if (Enum <= 66) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									elseif (Enum == 67) then
										Stk[Inst[2]] = Inst[3];
									else
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 69) then
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum > 70) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 74) then
								if (Enum <= 72) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								elseif (Enum == 73) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 76) then
								if (Enum > 75) then
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local T;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 77) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 91) then
							if (Enum <= 84) then
								if (Enum <= 81) then
									if (Enum <= 79) then
										VIP = Inst[3];
									elseif (Enum == 80) then
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 82) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 83) then
									local A;
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum <= 87) then
								if (Enum <= 85) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum == 86) then
									local Step;
									local Index;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Index = Stk[A];
									Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 89) then
								if (Enum == 88) then
									local A = Inst[2];
									local Cls = {};
									for Idx = 1, #Lupvals do
										local List = Lupvals[Idx];
										for Idz = 0, #List do
											local Upv = List[Idz];
											local NStk = Upv[1];
											local DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								else
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 90) then
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 98) then
							if (Enum <= 94) then
								if (Enum <= 92) then
									local Edx;
									local Results;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum == 93) then
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local T;
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 96) then
								if (Enum > 95) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum > 97) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 101) then
							if (Enum <= 99) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum == 100) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 103) then
							if (Enum > 102) then
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum == 104) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 158) then
						if (Enum <= 131) then
							if (Enum <= 118) then
								if (Enum <= 111) then
									if (Enum <= 108) then
										if (Enum <= 106) then
											local A;
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Inst[2] < Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum == 107) then
											local B;
											local A;
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
										else
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Stk[Inst[2]] <= Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 109) then
										Stk[Inst[2]][Inst[3]] = Inst[4];
									elseif (Enum > 110) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 114) then
									if (Enum <= 112) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									elseif (Enum > 113) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = Inst[3];
										else
											VIP = VIP + 1;
										end
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 116) then
									if (Enum == 115) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum == 117) then
									local B;
									local T;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								end
							elseif (Enum <= 124) then
								if (Enum <= 121) then
									if (Enum <= 119) then
										local T;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									elseif (Enum > 120) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 122) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 123) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum <= 127) then
								if (Enum <= 125) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								elseif (Enum > 126) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 129) then
								if (Enum > 128) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = -Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								elseif (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 130) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 144) then
							if (Enum <= 137) then
								if (Enum <= 134) then
									if (Enum <= 132) then
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 133) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 135) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 136) then
									local T;
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 140) then
								if (Enum <= 138) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 139) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 142) then
								if (Enum == 141) then
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum == 143) then
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 151) then
							if (Enum <= 147) then
								if (Enum <= 145) then
									local B;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 146) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 149) then
								if (Enum == 148) then
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 150) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 154) then
							if (Enum <= 152) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 153) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 156) then
							if (Enum > 155) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum == 157) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 185) then
						if (Enum <= 171) then
							if (Enum <= 164) then
								if (Enum <= 161) then
									if (Enum <= 159) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 160) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 162) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 163) then
									Stk[Inst[2]]();
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 167) then
								if (Enum <= 165) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 166) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 169) then
								if (Enum == 168) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local Edx;
									local Results;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum > 170) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum <= 178) then
							if (Enum <= 174) then
								if (Enum <= 172) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								elseif (Enum == 173) then
									local A = Inst[2];
									do
										return Stk[A], Stk[A + 1];
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 176) then
								if (Enum > 175) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum > 177) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Stk[Inst[4]]];
							end
						elseif (Enum <= 181) then
							if (Enum <= 179) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							elseif (Enum > 180) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 183) then
							if (Enum > 182) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum == 184) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 198) then
						if (Enum <= 191) then
							if (Enum <= 188) then
								if (Enum <= 186) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 187) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 189) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 190) then
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 194) then
							if (Enum <= 192) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum == 193) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 196) then
							if (Enum == 195) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 197) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 205) then
						if (Enum <= 201) then
							if (Enum <= 199) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 200) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 203) then
							if (Enum > 202) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum == 204) then
							local B;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 208) then
						if (Enum <= 206) then
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum == 207) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local T;
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 210) then
						if (Enum == 209) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 211) then
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 318) then
					if (Enum <= 265) then
						if (Enum <= 238) then
							if (Enum <= 225) then
								if (Enum <= 218) then
									if (Enum <= 215) then
										if (Enum <= 213) then
											if (Inst[2] < Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum == 214) then
											local B;
											local A;
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										else
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Inst[2] < Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 216) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 217) then
										local B;
										local T;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 221) then
									if (Enum <= 219) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									elseif (Enum > 220) then
										local A;
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 223) then
									if (Enum == 222) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									elseif (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 224) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 231) then
								if (Enum <= 228) then
									if (Enum <= 226) then
										do
											return Stk[Inst[2]];
										end
									elseif (Enum == 227) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local A;
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] < Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 229) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 230) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Stk[Inst[2]] <= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 234) then
								if (Enum <= 232) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 233) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 236) then
								if (Enum == 235) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum == 237) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 251) then
							if (Enum <= 244) then
								if (Enum <= 241) then
									if (Enum <= 239) then
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
									elseif (Enum > 240) then
										local A;
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 242) then
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 243) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 247) then
								if (Enum <= 245) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum == 246) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 249) then
								if (Enum > 248) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum > 250) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 258) then
							if (Enum <= 254) then
								if (Enum <= 252) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 253) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 256) then
								if (Enum > 255) then
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum == 257) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 261) then
							if (Enum <= 259) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 260) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 263) then
							if (Enum == 262) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local B;
								local T;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum > 264) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 291) then
						if (Enum <= 278) then
							if (Enum <= 271) then
								if (Enum <= 268) then
									if (Enum <= 266) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 267) then
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									else
										local T;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum <= 269) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 270) then
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 274) then
								if (Enum <= 272) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								elseif (Enum > 273) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 276) then
								if (Enum > 275) then
									local T;
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 277) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							end
						elseif (Enum <= 284) then
							if (Enum <= 281) then
								if (Enum <= 279) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								elseif (Enum == 280) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 282) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							elseif (Enum == 283) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 287) then
							if (Enum <= 285) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 286) then
								local A;
								local K;
								local B;
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 289) then
							if (Enum > 288) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum > 290) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 304) then
						if (Enum <= 297) then
							if (Enum <= 294) then
								if (Enum <= 292) then
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 293) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 295) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 296) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Edx;
								local Results, Limit;
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 300) then
							if (Enum <= 298) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum == 299) then
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 302) then
							if (Enum > 301) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 303) then
							local B;
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 311) then
						if (Enum <= 307) then
							if (Enum <= 305) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
							elseif (Enum == 306) then
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 309) then
							if (Enum == 308) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum > 310) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 314) then
						if (Enum <= 312) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						elseif (Enum > 313) then
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 316) then
						if (Enum > 315) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A;
							local K;
							local B;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum > 317) then
						local Edx;
						local Results;
						local A;
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Stk[A + 1])};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 371) then
					if (Enum <= 344) then
						if (Enum <= 331) then
							if (Enum <= 324) then
								if (Enum <= 321) then
									if (Enum <= 319) then
										if (Stk[Inst[2]] > Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 320) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									else
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 322) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 323) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 327) then
								if (Enum <= 325) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 326) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								end
							elseif (Enum <= 329) then
								if (Enum > 328) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 330) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum <= 337) then
							if (Enum <= 334) then
								if (Enum <= 332) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum > 333) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 335) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 336) then
								local B;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 340) then
							if (Enum <= 338) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Enum == 339) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 342) then
							if (Enum > 341) then
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum == 343) then
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 357) then
						if (Enum <= 350) then
							if (Enum <= 347) then
								if (Enum <= 345) then
									local B;
									local T;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								elseif (Enum == 346) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 348) then
								if (Stk[Inst[2]] > Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = VIP + Inst[3];
								end
							elseif (Enum > 349) then
								local B;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 353) then
							if (Enum <= 351) then
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum == 352) then
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local Edx;
								local Results;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 355) then
							if (Enum > 354) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum == 356) then
							do
								return;
							end
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 364) then
						if (Enum <= 360) then
							if (Enum <= 358) then
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum > 359) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 362) then
							if (Enum > 361) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum > 363) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 367) then
						if (Enum <= 365) then
							Stk[Inst[2]] = {};
						elseif (Enum > 366) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 369) then
						if (Enum > 368) then
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = -Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum > 370) then
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						local B;
						local T;
						local A;
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						T = Stk[A];
						B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					end
				elseif (Enum <= 398) then
					if (Enum <= 384) then
						if (Enum <= 377) then
							if (Enum <= 374) then
								if (Enum <= 372) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								elseif (Enum == 373) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 375) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 376) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 380) then
							if (Enum <= 378) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 379) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 382) then
							if (Enum > 381) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum > 383) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 391) then
						if (Enum <= 387) then
							if (Enum <= 385) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] > Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = VIP + Inst[3];
								end
							elseif (Enum > 386) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 400) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 389) then
							if (Enum > 388) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 390) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 394) then
						if (Enum <= 392) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 393) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 396) then
						if (Enum == 395) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							Stk[Inst[2]] = -Stk[Inst[3]];
						end
					elseif (Enum > 397) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local A;
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 411) then
					if (Enum <= 404) then
						if (Enum <= 401) then
							if (Enum <= 399) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum == 400) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 402) then
							local A;
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						elseif (Enum > 403) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 407) then
						if (Enum <= 405) then
							local A;
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 406) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 409) then
						if (Enum > 408) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum > 410) then
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local Results;
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum <= 418) then
					if (Enum <= 414) then
						if (Enum <= 412) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 413) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 416) then
						if (Enum > 415) then
							Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum > 417) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] ~= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = #Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 421) then
					if (Enum <= 419) then
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					elseif (Enum > 420) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return Stk[Inst[2]];
						end
					else
						local B;
						local A;
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 423) then
					if (Enum > 422) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						local Edx;
						local Results;
						local A;
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Stk[A + 1])};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum == 424) then
					Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
				else
					local A;
					A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A] = Stk[A]();
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					if (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!7D012Q0003043Q007469636B03023Q005F4703053Q00466F72676503043Q005461627303063Q004D696E696E67026Q003E4003043Q007761726E03433Q005B466F726765204D696E696E675D2054696D656F75742077616974696E6720666F7220466F7267652E4D696E696E67207461623B2061626F7274696E67206C6F61642E03043Q007461736B03043Q0077616974026Q00E03F03043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030A3Q0052756E5365727669636503113Q005265706C69636174656453746F7261676503093Q00576F726B7370616365030B3Q004C6F63616C506C6179657203083Q005261796669656C64030A3Q004175746F4D696E696E670100030D3Q0053656C65637465644172656173030D3Q0053656C6563746564526F636B73030C3Q0053656C65637465644F726573030E3Q00526F636B5072696F726974696573030F3Q005072696F72697479456E61626C65642Q0103143Q005072696F726974795363616E496E74657276616C029A5Q99B93F03163Q005072696F72697479537769746368432Q6F6C646F776E026Q00F03F03143Q005072696F72697479536B6970432Q6F6C646F776E026Q00204003113Q005072696F726974794477652Q6C54696D65026Q001040030E3Q00526F636B4F726546696C7465727303043Q00526F636B0003043Q004F72657303093Q0044656275674D6F646503083Q0044697374616E6365026Q00184003093Q004D696E6544656C617903063Q00486569676874029A5Q991D40030A3Q00466C696768744D6F646503053Q0042656C6F77030A3Q0047686F737453702Q6564026Q003940030B3Q0047686F73744F2Q66736574026Q000CC0030B3Q004D696E696E6752616E6765025Q00409F4003133Q00446972656374436861736544697374616E6365025Q00C07240030B3Q005A6F6E65456E61626C6564030A3Q005A6F6E6543656E74657203013Q0058028Q0003013Q005903013Q005A03083Q005A6F6E654C65667403093Q005A6F6E65526967687403093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B03063Q005A6F6E655570026Q002E4003083Q005A6F6E65446F776E026Q00144003123Q004D61696E74656E616E6365456E61626C656403133Q004D61696E74656E616E6365496E74657276616C026Q004E4003183Q004D61696E74656E616E63654D696E655468726573686F6C64026Q00794003093Q0053702Q65644E656172029A5Q99E93F030B3Q0053702Q6564536C6F776D6F026Q330740030D3Q0053702Q6564412Q70726F61636803083Q0053702Q6564466172026Q00F83F03113Q005361666548656967687444656661756C74025Q00806640030F3Q0053616665486569676874537061776E030E3Q005361666548656967687449646C6503103Q00537061776E436865636B526164697573025Q00407F4003103Q00526F746174696F6E446561645A6F6E65026Q000C40030F3Q004F7265436865636B456E61626C6564030D3Q004F7265436865636B4C6576656C026Q004440030D3Q004F7265536B69704E6F7469667903143Q00412Q6C6F774F726546696C746572427970612Q7303113Q00557365476C6F62616C46612Q6C6261636B03133Q00526F636B52656672657368496E74657276616C03183Q00526F636B526566726573684E6F54617267657444656C6179026Q000440030A3Q0043616D6572614D6F6465030A3Q004C6F636B546172676574030C3Q0043616D657261486569676874026Q004240030E3Q0043616D65726144697374616E6365026Q002440030A3Q0043616D6572615369646503193Q004175746F5472696D496E76616C696453656C656374696F6E7303103Q00486F72697A6F6E74616C4F2Q6673657403163Q00526F746174696F6E446561645A6F6E6554726176656C030F3Q004D696E6544656C61794A692Q746572026Q00D03F030E3Q00537475636B446574656374696F6E03073Q00456E61626C6564030B3Q005468726573686F6C644C31030B3Q005468726573686F6C644C32026Q004940030B3Q005468726573686F6C644C33026Q005440030D3Q0054696D655468726573686F6C64026Q003440030E3Q00476C6974636844697374616E6365026Q001C4003103Q005265636F76657279432Q6F6C646F776E03113Q00506F736974696F6E5468726573686F6C6403153Q00506F736974696F6E436865636B496E74657276616C026Q00084003053Q00706169727303043Q007479706503053Q007461626C65030B3Q0043752Q72656E74526F636B030C3Q0043752Q72656E745068617365030A3Q00536B69704672616D6573030E3Q00536B69704D696E654672616D6573030D3Q004C6F636B65644D696E65506F73030E3Q004C617374526F636B536561726368030D3Q004C6173744E6F526F636B4C6F6703103Q0053652Q73696F6E537461727454696D65030A3Q00546F74616C4D696E656403133Q004C6173744D61696E74656E616E636554696D6503103Q004D61696E74656E616E6365436F756E74030E3Q004C61737446696C746572526F636B03113Q004C6173744F7265536B69704E6F74696679030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B73030F3Q004C617374526F636B52656672657368030D3Q004E6F54617267657453696E636503153Q0049676E6F72654F726546696C74657273556E74696C03123Q004C6173745072696F7269747953776974636803113Q005072696F726974794C6F636B556E74696C03143Q004C6173745072696F72697479526F636B5479706503153Q005072696F7269747954797065432Q6F6C646F776E7303123Q0043616D6572615368616B65526573746F7265030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030D3Q004C617374536B69705265736574030E3Q004C6173744C2Q6F6B54617267657403103Q004C61737446696C746572536F7572636503153Q004C617374416C72656164794D696E696E6754696D65030D3Q0050656E64696E6753776974636803113Q004C61737450656E64696E6753776974636803123Q004F726967696E616C43616D6572615479706503103Q0043616D657261436F2Q6E656374696F6E030A3Q004C617374526F636B4850030B3Q004C617374526F636B52656603123Q004D696E657353696E636548504368616E6765030E3Q00537475636B436865636B54696D65030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D65030E3Q004C32412Q74656D7074436F756E74030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D65030F3Q005072696F72697479536C696465727303113Q004C6173745072696F72697479436865636B03143Q004C61737454726176656C4C2Q6F6B54617267657403053Q00417265617303053Q00526F636B73030C3Q004D696E696E67436F6E66696703083Q00496E7374616E63652Q033Q006E657703063Q00466F6C64657203063Q0073656C65637403053Q007063612Q6C03073Q0044657374726F79030D3Q0043752Q72656E7443616D657261030D3Q0043726561746553656374696F6E030B3Q004175746F204D696E696E6703103Q004175746F4D696E696E67546F2Q676C65030C3Q00437265617465546F2Q676C6503043Q004E616D6503123Q00456E61626C65204175746F204D696E696E67030C3Q0043752Q72656E7456616C756503043Q00466C616703103Q004D696E696E674175746F546F2Q676C6503083Q0043612Q6C6261636B03143Q00537475636B446574656374696F6E546F2Q676C6503113Q00416E74692D537475636B2053797374656D031A3Q004D696E696E67537475636B446574656374696F6E546F2Q676C65031B3Q00506F736974696F6E436865636B496E74657276616C536C69646572030C3Q00437265617465536C6964657203183Q00537475636B20436865636B20496E74657276616C2028732903053Q0052616E676503093Q00496E6372656D656E7403063Q0053752Q66697803013Q007303183Q004D696E696E67537475636B436865636B496E74657276616C03173Q00506F736974696F6E5468726573686F6C64536C69646572031C3Q00537475636B204D6F7665205468726573686F6C64202873747564732903063Q0020737475647303183Q004D696E696E67537475636B4D6F76655468726573686F6C64030C3Q0043726561746542752Q746F6E030D3Q00466F72636520436C65616E7570030D3Q0053652Q73696F6E205374617473030F3Q004172656120262053652Q74696E677303053Q007072696E7403283Q005B466F726765204D696E696E675D20526F636B20536F757263653A20412Q6C204172656173202D20030B3Q0020726F636B20747970657303293Q005B466F726765204D696E696E675D204F726520536F757263653A20412Q6C2049736C616E6473202D2003053Q00206F726573031C3Q005B466F726765204D696E696E675D20526F636B20536F757263653A2003093Q00206172656173202D20030C3Q004172656144726F70646F776E030E3Q0043726561746544726F70646F776E031B3Q004D696E696E6720417265617320284D756C74692D53656C6563742903073Q004F7074696F6E73030D3Q0043752Q72656E744F7074696F6E030F3Q004D756C7469706C654F7074696F6E73030B3Q004D696E696E67417265617303093Q00417265614C6162656C030B3Q004372656174654C6162656C03013Q002003063Q00636F6E63617403023Q002C2003093Q00412Q6C204172656173030E3Q00205265667265736820417265617303153Q0020436C65617220412Q6C2053656C656374696F6E73030D3Q005265667265736820526F636B73030C3Q0052656672657368204F726573030F3Q00205363616E204172656120496E666F03123Q00466C696768744D6F646544726F70646F776E030B3Q00466C69676874204D6F646503053Q0041626F766503103Q004D696E696E67466C696768744D6F646503123Q0043616D6572614D6F646544726F70646F776E030B3Q0043616D657261204D6F646503043Q004E6F6E65030B3Q0046697865644F2Q6673657403103Q004D696E696E6743616D6572614D6F646503113Q0054696D696E672026204D6F76656D656E74030F3Q004D696E6544656C6179536C69646572031A3Q004D696E652044656C61792028626173652C207365636F6E647329029A5Q99A93F026Q33E33F027B14AE47E17A843F030F3Q004D696E696E674D696E6544656C617903153Q004D696E6544656C61794A692Q746572536C6964657203153Q004D696E652044656C6179204A692Q746572204D6178029A5Q99D93F03153Q004D696E696E674D696E6544656C61794A692Q74657203163Q00486F72697A6F6E74616C4F2Q66736574536C69646572031A3Q00486F72697A6F6E74616C204F2Q66736574202873747261666529026Q0024C003163Q004D696E696E67486F72697A6F6E74616C4F2Q66736574031C3Q00526F746174696F6E446561645A6F6E6554726176656C536C69646572031B3Q00526F746174696F6E2044656164205A6F6E65202874726176656C29031C3Q004D696E696E67526F746174696F6E446561645A6F6E6554726176656C03103Q005461726765742053656C656374696F6E030C3Q00526F636B44726F70646F776E03193Q00526F636B20547970657320284D756C74692D53656C6563742903143Q00284E6F20726F636B7320617661696C61626C6529030B3Q004D696E696E67526F636B7303093Q00526F636B4C6162656C030F3Q00286E6F6E652073656C656374656429030E3Q00526F636B436F756E744C6162656C03203Q00F09F938A202873656C65637420726F636B7320746F20732Q6520636F756E7429030F3Q005072696F726974792053797374656D030E3Q005072696F72697479546F2Q676C65030F3Q00456E61626C65205072696F7269747903143Q004D696E696E675072696F72697479546F2Q676C65030D3Q005072696F726974794C6162656C03203Q002053656C65637420322B20726F636B7320746F20736574207072696F72697479030E3Q002052657665727365204F72646572031A3Q005072696F726974795363616E496E74657276616C536C69646572031A3Q005072696F72697479205363616E20496E74657276616C20287329031A3Q004D696E696E675072696F726974795363616E496E74657276616C031C3Q005072696F72697479537769746368432Q6F6C646F776E536C69646572031C3Q005072696F726974792053776974636820432Q6F6C646F776E20287329031C3Q004D696E696E675072696F72697479537769746368432Q6F6C646F776E03173Q005072696F726974794477652Q6C54696D65536C6964657203173Q005072696F72697479204477652Q6C2054696D652028732903173Q004D696E696E675072696F726974794477652Q6C54696D65031A3Q005072696F72697479536B6970432Q6F6C646F776E536C69646572031A3Q005072696F7269747920536B6970204F6C6420526F636B20287329031A3Q004D696E696E675072696F72697479536B6970432Q6F6C646F776E03103Q00436C656172205072696F726974696573030B3Q004F726544726F70646F776E03163Q00476C6F62616C204F726573202846612Q6C6261636B2903133Q002853656C656374206172656120666972737429030A3Q004D696E696E674F72657303083Q004F72654C6162656C03183Q00476C6F62616C204F726573202866612Q6C6261636B293A2003113Q00436C65617220476C6F62616C204F72657303173Q00557365476C6F62616C46612Q6C6261636B546F2Q676C6503133Q0055736520476C6F62616C2046612Q6C6261636B03173Q004D696E696E67557365476C6F62616C46612Q6C6261636B03113Q0041637469766546696C7465724C6162656C03133Q004163746976652046696C7465723A204E6F6E6503113Q005472696D496E76616C6964546F2Q676C6503233Q004175746F2D7472696D20696E76616C69642073656C656374696F6E732028736166652903153Q004D696E696E674175746F5472696D496E76616C6964031C3Q005065722D526F636B204F72652046696C746572732028536C6F747329030F3Q0046696C746572536C6F7431526F636B030D3Q00536C6F742031202D20526F636B03063Q00286E6F6E652903153Q004D696E696E6746696C746572536C6F7431526F636B030E3Q0046696C746572536C6F74314F7265030D3Q00536C6F742031202D204F72657303143Q004D696E696E6746696C746572536C6F74314F726503103Q0046696C746572536C6F74314C6162656C030B3Q00E286922028656D70747929030F3Q0046696C746572536C6F7432526F636B030D3Q00536C6F742032202D20526F636B03153Q004D696E696E6746696C746572536C6F7432526F636B027Q0040030E3Q0046696C746572536C6F74324F7265030D3Q00536C6F742032202D204F72657303143Q004D696E696E6746696C746572536C6F74324F726503103Q0046696C746572536C6F74324C6162656C030F3Q0046696C746572536C6F7433526F636B030D3Q00536C6F742033202D20526F636B03153Q004D696E696E6746696C746572536C6F7433526F636B030E3Q0046696C746572536C6F74334F7265030D3Q00536C6F742033202D204F72657303143Q004D696E696E6746696C746572536C6F74334F726503103Q0046696C746572536C6F74334C6162656C03163Q00436C65617220412Q6C20536C6F742046696C7465727303243Q0064595A5F20412Q706C7920536C6F742054656D706C6174657320285065722D526F636B29030E3Q00496365202B204C6967687469746503063Q0049636569746503073Q00536E6F7769746503073Q0053616E6374697303083Q0056656C6368697265030C3Q0046726F737420466F2Q73696C03083Q004C6967687469746503113Q0049636520284E6F204C6967687469746529030A3Q0044656D6F6E204172656103083Q0044656D6F6E69746503083Q004461726B7279746503083Q004D61676D6169746503063Q0048656176656E03093Q0048656176656E697465030A3Q0047617267616E7475616E03083Q00537572796166616C030B3Q00457468657265616C69746503093Q00436C65617220412Q6C03133Q004F726554656D706C61746544726F70646F776E03233Q00476C6F62616C204F72652054656D706C617465732028517569636B2053656C6563742903113Q004D696E696E674F726554656D706C617465030E3Q004F7265436865636B546F2Q676C6503233Q00536B697020526F636B206966204F7265204E6F74204D61746368202861742034302529030E3Q004D696E696E674F7265436865636B03133Q004F7265536B69704E6F74696679546F2Q676C6503123Q004E6F74696679206F6E204F726520536B697003133Q004D696E696E674F7265536B69704E6F7469667903153Q004F726546696C746572427970612Q73546F2Q676C65031F3Q00412Q6C6F772046696C74657220427970612Q7320286E6F207461726765742903153Q004D696E696E674F726546696C746572427970612Q73030F3Q0043726561746550617261677261706803053Q005469746C6503123Q0020416476616E6365642053652Q74696E677303073Q00436F6E74656E74035C3Q0053702Q65642C204865696768742C20616E64206F746865722074756E696E6720736C69646572732061726520696E2074686520504C415945522074616220756E646572204D696E696E6720416476616E6365642073656374696F6E2E03133Q004D696E696E6744656661756C74436F6E66696703103Q004D696E696E675549456C656D656E7473030B3Q0052657365744D696E696E67030A3Q0053746F704D696E696E6703073Q00436C65616E757003063Q00696E73657274030D3Q00556E6C6F6164436C65616E7570030D3Q004D696E696E67204D6F64756C65030C3Q0076342E30204C6F616465642103083Q004475726174696F6E03263Q005B54686520466F7267655D204D696E696E67206D6F64756C652076342E30206C6F61646564210079062Q001269012Q00014Q00033Q000100020012692Q0100023Q00204D2Q01000100030006082Q01001100013Q00044F3Q001100010012692Q0100023Q00204D2Q010001000300204D2Q01000100040006082Q01001100013Q00044F3Q001100010012692Q0100023Q00204D2Q010001000300204D2Q010001000400204D2Q010001000500060D2Q01001F0001000100044F3Q001F00010012692Q0100014Q00030001000100022Q00792Q0100013Q000ED50006001A0001000100044F3Q001A00010012692Q0100073Q001243000200084Q007B2Q01000200012Q0064012Q00013Q0012692Q0100093Q00204D2Q010001000A0012430002000B4Q007B2Q010002000100044F3Q000200010012692Q01000C3Q0020BA00010001000D00122Q0003000E6Q00010003000200122Q0002000C3Q00202Q00020002000D00122Q0004000F6Q00020004000200122Q0003000C3Q00202Q00030003000D00122Q000500104Q00440003000500020012360104000C3Q00202Q00040004000D00122Q000600116Q00040006000200202Q00050001001200068201063Q000100022Q0090012Q00054Q0090012Q00013Q001269010700023Q00204D01070007000300204D01080007000400204D01080008000500204D010900070013000682010A0001000100022Q0090012Q00094Q0090012Q00073Q000682010B0002000100012Q0090012Q00074Q003D000C000B6Q000D000E6Q000F3Q001E00302Q000F001400154Q00105Q00102Q000F001600104Q00105Q00102Q000F001700104Q00105Q00102Q000F001800102Q006D01105Q0010E1000F0019001000306D000F001A001B00306D000F001C001D00306D000F001E001F00306D000F0020002100306D000F002200232Q0007011000036Q00113Q000200302Q0011002500264Q00125Q00102Q0011002700124Q00123Q000200302Q0012002500264Q00135Q00102Q0012002700134Q00133Q000200302Q0013002500264Q00145Q00102Q0013002700144Q0010000300010010E1000F00240010003017000F0028001500302Q000F0029002A00302Q000F002B001D00302Q000F002C002D00302Q000F002E002F00302Q000F0030003100302Q000F0032003300302Q000F0034003500302Q000F0036003700302Q000F003800154Q00103Q000300302Q0010003A003B00302Q0010003C003B00302Q0010003D003B00102Q000F0039001000302Q000F003E003100302Q000F003F003100302Q000F0040003100302Q000F0041003100302Q000F0042004300302Q000F0044004500302Q000F0046001B00302Q000F0047004800302Q000F0049004A00302Q000F004B004C00302Q000F004D004E00302Q000F004F000B00302Q000F0050005100302Q000F0052005300302Q000F0054005300302Q000F0055005300302Q000F0056005700302Q000F0058005900302Q000F005A001B00302Q000F005B005C00302Q000F005D001B00302Q000F005E001500302Q000F005F001B00302Q000F0060002A00302Q000F0061006200302Q000F0063006400302Q000F0065006600302Q000F0067006800302Q000F0069004500302Q000F006A001500302Q000F006B003B00302Q000F006C005100302Q000F006D006E4Q00103Q000900302Q00100070001B00302Q00100071003100302Q00100072007300302Q00100074007500302Q00100076007700302Q00100078007900302Q0010007A004500302Q0010007B004500302Q0010007C007D00102Q000F006F00104Q00105Q00122Q0011007E6Q0012000F6Q00110002001300044Q00AE00010012690116007F4Q0090011700154Q00310016000200020026DF001600AD0001008000044F3Q00AD00012Q006D01166Q00B900100014001600122Q0016007E6Q001700156Q00160002001800044Q00AA00012Q00C0001B001000142Q007B001B0019001A0006AA001600A80001000200044F3Q00A8000100044F3Q00AE00012Q007B0010001400150006AA0011009D0001000200044F3Q009D00012Q006D01113Q001C00303801110081002600302Q00110082003B00302Q00110083003B00302Q00110084003B00302Q00110085002600302Q00110086002600302Q00110087002600308301110088003B00302Q00110089003B00302Q0011008A003B00302Q0011008B003B00302Q0011008C002600302Q0011008D003B4Q00125Q00102Q0011008E00124Q00125Q00102Q0011008F001200306D00110090003B00306D00110091002600306D00110092003B00306D00110093003B00306D00110094003B00306D0011009500262Q006D01125Q0010E100110096001200306D0011009700262Q006D01125Q0010E10011009800122Q006D01125Q0010E10011009900120030380111009A003B00302Q0011009B002600302Q0011009C002600302Q0011009D003B00302Q0011009E001500302Q0011009F003B00302Q001100A00026003038011100A1002600302Q001100A2002600302Q001100A3002600302Q001100A4003B00302Q001100A5003B00302Q001100A6003B00302Q001100A7003B0030EA001100A8003B00302Q001100A9002600302Q001100AA003B4Q00125Q00102Q001100AB001200302Q001100AC003B00302Q001100AD00264Q00128Q00133Q000300302Q001300AE003B00306D001300AF003B00306D00130027003B2Q001A0114001C4Q006D011D6Q001A011E001F3Q0002B3002000033Q001269012100023Q00204D0121002100030010E1002100B0001000068201210004000100012Q0090012Q00044Q006D01225Q0012430023003B4Q0090012400213Q00068201210005000100032Q0090012Q00224Q0090012Q00234Q0090012Q00244Q007400255Q00122Q0026003B6Q002700276Q00285Q00122Q0029003B6Q002A002A6Q002B5Q000682012C0006000100012Q0090012Q00043Q000682012D0007000100012Q0090012Q00044Q00900127002D3Q000682012D0008000100042Q0090012Q002B4Q0090012Q00254Q0090012Q00264Q0090012Q00273Q001206012E00B13Q00202Q002E002E00B200122Q002F00B36Q002E0002000200122Q002F00B43Q00122Q0030001F3Q00122Q003100B53Q00068201320009000100012Q0090012Q002E4Q00EC003100326Q002F3Q000200122Q003000B43Q00122Q0031001F3Q00122Q003200B53Q0006820133000A000100012Q0090012Q002E4Q0041003200334Q008A01303Q00020020180131002E00B62Q007B0131000200010006820131000B000100022Q0090012Q002F4Q0090012Q00303Q0006820132000C000100022Q0090012Q00014Q0090012Q00313Q0006820133000D000100022Q0090012Q00014Q0090012Q00314Q0090012A00333Q0006820133000E000100032Q0090012Q00284Q0090012Q00294Q0090012Q002A3Q0006820134000F000100012Q0090012Q00013Q0002B3003500103Q0002B3003600113Q0002B3003700124Q006D01386Q006D01396Q006D013A5Q0002B3003B00133Q000682013C0014000100022Q0090012Q00104Q0090012Q003B3Q000682013D0015000100012Q0090012Q00133Q000682013E0016000100022Q0090012Q00064Q0090012Q00043Q0002B3003F00173Q0002B3004000184Q001A014100413Q0012430042003B4Q008B01435Q00068201440019000100042Q0090012Q002B4Q0090012Q003A4Q0090012Q00254Q0090012Q00383Q0006820145001A000100072Q0090012Q00414Q0090012Q00424Q0090012Q00044Q0090012Q00434Q0090012Q001A4Q0090012Q00444Q0090012Q001B3Q001243004600533Q0012430047003B3Q0006820148001B000100042Q0090012Q00474Q0090012Q00464Q0090012Q00044Q0090012Q00103Q00204D0149000400B7000682014A001C000100022Q0090012Q00494Q0090012Q00043Q000682014B001D000100072Q0090012Q00104Q0090012Q004A4Q0090012Q003C4Q0090012Q00114Q0090012Q00024Q0090012Q003E4Q0090012Q000C3Q000682014C001E000100032Q0090012Q00114Q0090012Q003C4Q0090012Q004A3Q000682014D001F000100012Q0090012Q00113Q000682014E0020000100012Q0090012Q00114Q006D014F5Q00068201500021000100012Q0090012Q004F3Q0002B3005100223Q00068201520023000100012Q0090012Q003A3Q00068201530024000100022Q0090012Q00044Q0090012Q00513Q00068201540025000100012Q0090012Q00533Q00068201550026000100012Q0090012Q001C3Q00068201560027000100052Q0090012Q00554Q0090012Q001C4Q0090012Q00104Q0090012Q00124Q0090012Q00543Q00068201570028000100012Q0090012Q00103Q00068201580029000100022Q0090012Q00354Q0090012Q00113Q0006820159002A000100022Q0090012Q00114Q0090012Q00353Q000682015A002B000100032Q0090012Q00114Q0090012Q00354Q0090012Q00103Q000682015B002C000100062Q0090012Q000D4Q0090012Q00104Q0090012Q00384Q0090012Q00124Q0090012Q000A4Q0090012Q00113Q000682015C002D000100032Q0090012Q00104Q0090012Q00114Q0090012Q005B3Q000682015D002E000100012Q0090012Q00113Q000682015E002F000100012Q0090012Q00113Q000682015F0030000100012Q0090012Q00113Q00068201600031000100022Q0090012Q00114Q0090012Q005F3Q00068201610032000100012Q0090012Q00113Q00068201620033000100012Q0090012Q00103Q00068201630034000100052Q0090012Q00124Q0090012Q00114Q0090012Q00514Q0090012Q00624Q0090012Q00103Q00068201640035000100012Q0090012Q00113Q00068201650036000100042Q0090012Q00104Q0090012Q00644Q0090012Q00114Q0090012Q000A3Q0002B3006600373Q00068201670038000100022Q0090012Q00104Q0090012Q00663Q00068201680039000100012Q0090012Q00103Q0006820169003A000100042Q0090012Q00504Q0090012Q00104Q0090012Q00514Q0090012Q00573Q000682016A003B0001000B2Q0090012Q00104Q0090012Q00514Q0090012Q003E4Q0090012Q000C4Q0090012Q00454Q0090012Q005D4Q0090012Q00584Q0090012Q00114Q0090012Q00504Q0090012Q00694Q0090012Q003C3Q000682016B003C0001000B2Q0090012Q003E4Q0090012Q000C4Q0090012Q00454Q0090012Q00584Q0090012Q00114Q0090012Q00504Q0090012Q00694Q0090012Q00104Q0090012Q00514Q0090012Q003C4Q0090012Q005D3Q001243006C003B3Q001243006D003B4Q001A016E006E3Q000682016F003D000100072Q0090012Q00114Q0090012Q003E4Q0090012Q000C4Q0090012Q00504Q0090012Q003C4Q0090012Q00104Q0090012Q006F3Q000682016E003E000100072Q0090012Q00104Q0090012Q00114Q0090012Q003E4Q0090012Q000C4Q0090012Q003C4Q0090012Q006F4Q0090012Q00363Q001243007000623Q001243007100063Q0012430072003B3Q0002B30073003F3Q000682017400400001000F2Q0090012Q00194Q0090012Q00034Q0090012Q00724Q0090012Q003C4Q0090012Q00104Q0090012Q00744Q0090012Q00734Q0090012Q00114Q0090012Q00704Q0090012Q003E4Q0090012Q000C4Q0090012Q00504Q0090012Q006C4Q0090012Q00714Q0090012Q00513Q00068201750041000100032Q0090012Q00194Q0090012Q003C4Q0090012Q00723Q00068201760042000100072Q0090012Q00104Q0090012Q006C4Q0090012Q006D4Q0090012Q003C4Q0090012Q00034Q0090012Q003E4Q0090012Q006E3Q00068201770043000100012Q0090012Q00063Q00068201780044000100032Q0090012Q00144Q0090012Q003C4Q0090012Q00043Q00068201790045000100052Q0090012Q00144Q0090012Q00784Q0090012Q00104Q0090012Q00044Q0090012Q003C3Q000682017A0046000100022Q0090012Q00144Q0090012Q003C3Q000682017B0047000100032Q0090012Q003E4Q0090012Q000C4Q0090012Q00153Q000682017C00480001000B2Q0090012Q007B4Q0090012Q007A4Q0090012Q00164Q0090012Q00174Q0090012Q00184Q0090012Q00204Q0090012Q001A4Q0090012Q001B4Q0090012Q00434Q0090012Q00754Q0090012Q003C3Q000682017D0049000100082Q0090012Q00104Q0090012Q00114Q0090012Q006D4Q0090012Q003F4Q0090012Q003C4Q0090012Q007A4Q0090012Q00784Q0090012Q00163Q000682017E004A000100012Q0090012Q00103Q000682017F004B000100112Q0090012Q00794Q0090012Q00404Q0090012Q003C4Q0090012Q007E4Q0090012Q00484Q0090012Q00104Q0090012Q00114Q0090012Q00514Q0090012Q00624Q0090012Q00634Q0090012Q00354Q0090012Q00524Q0090012Q00654Q0090012Q00644Q0090012Q000A4Q0090012Q00764Q0090012Q00153Q0006820180004C0001000B2Q0090012Q00174Q0090012Q00184Q0090012Q00754Q0090012Q007B4Q0090012Q007A4Q0090012Q00154Q0090012Q004E4Q0090012Q004C4Q0090012Q00114Q0090012Q006D4Q0090012Q003C3Q0006820181004D000100242Q0090012Q00204Q0090012Q00174Q0090012Q00114Q0090012Q003C4Q0090012Q004B4Q0090012Q004D4Q0090012Q00784Q0090012Q00744Q0090012Q00184Q0090012Q00024Q0090012Q00104Q0090012Q003E4Q0090012Q001E4Q0090012Q001D4Q0090012Q001F4Q0090012Q00774Q0090012Q007D4Q0090012Q00594Q0090012Q005A4Q0090012Q000C4Q0090012Q007B4Q0090012Q00364Q0090012Q00514Q0090012Q006B4Q0090012Q005F4Q0090012Q00614Q0090012Q006D4Q0090012Q000F4Q0090012Q005E4Q0090012Q006A4Q0090012Q00694Q0090012Q00454Q0090012Q00634Q0090012Q00504Q0090012Q005C4Q0090012Q007F3Q0006820182004E000100062Q0090012Q000A4Q0090012Q00104Q0090012Q00814Q0090012Q00564Q0090012Q00804Q0090012Q00553Q0020930083000800B800122Q008500B96Q00830085000100202Q0083000800BB4Q00853Q000400302Q008500BC00BD00302Q008500BE001500302Q008500BF00C00006820186004F000100012Q0090012Q00823Q001041018500C100864Q00830085000200102Q001200BA008300202Q0083000800BB4Q00853Q000400302Q008500BC00C300302Q008500BE001B00302Q008500BF00C400068201860050000100012Q0090012Q00103Q00105E008500C100864Q00830085000200102Q001200C2008300202Q0083000800C64Q00853Q000700302Q008500BC00C74Q008600023Q00122Q0087000B3Q00122Q008800686Q0086000200010010E1008500C8008600308E008500C9000B00302Q008500CA00CB00202Q00860010006F00202Q00860086007C00102Q008500BE008600302Q008500BF00CC00068201860051000100012Q0090012Q00103Q00105E008500C100864Q00830085000200102Q001200C5008300202Q0083000800C64Q00853Q000700302Q008500BC00CE4Q008600023Q00122Q0087001F3Q00122Q008800776Q0086000200010010E1008500C8008600308E008500C9000B00302Q008500CA00CF00202Q00860010006F00202Q00860086007B00102Q008500BE008600302Q008500BF00D000068201860052000100012Q0090012Q00103Q0010E1008500C100862Q006001830085000200102Q001200CD008300202Q0083000800D14Q00853Q000200302Q008500BC00D200068201860053000100022Q0090012Q007D4Q0090012Q000A3Q001090008500C100864Q00830085000100202Q0083000800D14Q00853Q000200302Q008500BC00D300068201860054000100032Q0090012Q00114Q0090012Q003F4Q0090012Q000A3Q001077018500C100864Q00830085000100202Q0083000800B800122Q008500D46Q008300850001000682010D0055000100052Q0090012Q002B4Q0090012Q00384Q0090012Q00104Q0090012Q002D4Q0090012Q002C3Q000682010E0056000100032Q0090012Q00394Q0090012Q00334Q0090012Q00124Q001E018300216Q0083000100024Q002200833Q00202Q0083001000164Q008300833Q00262Q008300ED0201003B00044F3Q00ED02012Q00900183000D4Q0053008400016Q0083000200014Q0083000E6Q008400016Q00830002000100122Q008300D53Q00122Q008400D66Q008500383Q00122Q008600D76Q0084008400862Q007B01830002000100127D018300D53Q00122Q008400D86Q008500393Q00122Q008600D96Q0084008400864Q00830002000100044Q00FC02012Q00900183000D4Q0016008400016Q0083000200014Q0083000E6Q008400016Q00830002000100122Q008300D53Q00122Q008400DA3Q00202Q0085001000164Q008500853Q00122Q008600DB4Q0034008700383Q001243008800D74Q00ED0084008400882Q007B0183000200010020180183000800DD2Q001300853Q000600302Q008500BC00DE00102Q008500DF002200202Q00860010001600102Q008500E0008600302Q008500E1001B00302Q008500BF00E200068201860057000100062Q0090012Q00114Q0090012Q00104Q0090012Q000D4Q0090012Q00124Q0090012Q00384Q0090012Q003C3Q0010E1008500C100862Q00440083008500020010E1001200DC00830020180183000800E4001243008500E53Q00204D0186001000162Q0034008600863Q000ED5003B001B0301008600044F3Q001B0301001269018600803Q0020F60086008600E600202Q00870010001600122Q008800E76Q00860088000200062Q0086001C0301000100044F3Q001C0301001243008600E84Q00ED0085008500862Q006001830085000200102Q001200E3008300202Q0083000800D14Q00853Q000200302Q008500BC00E900068201860058000100052Q0090012Q003D4Q0090012Q00224Q0090012Q00214Q0090012Q00124Q0090012Q000A3Q001090008500C100864Q00830085000100202Q0083000800D14Q00853Q000200302Q008500BC00EA000682018600590001000A2Q0090012Q00104Q0090012Q00124Q0090012Q00114Q0090012Q000D4Q0090012Q00384Q0090012Q000E4Q0090012Q00394Q0090012Q00634Q0090012Q000A4Q0090012Q003C3Q001090008500C100864Q00830085000100202Q0083000800D14Q00853Q000200302Q008500BC00EB0006820186005A000100022Q0090012Q003D4Q0090012Q005B3Q001090008500C100864Q00830085000100202Q0083000800D14Q00853Q000200302Q008500BC00EC0006820186005B000100062Q0090012Q003D4Q0090012Q000E4Q0090012Q00394Q0090012Q00104Q0090012Q00124Q0090012Q000A3Q001090008500C100864Q00830085000100202Q0083000800D14Q00853Q000200302Q008500BC00ED0006820186005C000100052Q0090012Q00104Q0090012Q002D4Q0090012Q00384Q0090012Q00334Q0090012Q000A3Q001090008500C100864Q00830085000100202Q0083000800DD4Q00853Q000500302Q008500BC00EF2Q006D018600023Q001243008700F03Q0012430088002F4Q00050086000200010010E1008500DF00862Q006D018600013Q00204D01870010002E2Q00050086000100010010E1008500E0008600306D008500BF00F10006820186005D000100012Q0090012Q00103Q0010E1008500C100862Q006001830085000200102Q001200EE008300202Q0083000800DD4Q00853Q000500302Q008500BC00F32Q0072018600033Q00122Q008700F43Q00122Q008800643Q00122Q008900F56Q0086000300010010E1008500DF00862Q006D018600013Q00204D0187001000632Q00050086000100010010E1008500E0008600306D008500BF00F60006820186005E000100042Q0090012Q00104Q0090012Q004C4Q0090012Q004B4Q0090012Q003C3Q001031018500C100864Q00830085000200102Q001200F2008300202Q0083000800B800122Q008500F76Q00830085000100202Q0083000800C64Q00853Q000700302Q008500BC00F94Q008600023Q001243008700FA3Q001243008800FB4Q00050086000200010010E1008500C8008600306D008500C900FC00306D008500CA00CB00204D01860010002B0010E1008500BE008600306D008500BF00FD0006820186005F000100012Q0090012Q00103Q00105E008500C100864Q00830085000200102Q001200F8008300202Q0083000800C64Q00853Q000700302Q008500BC00FF4Q008600023Q00122Q0087003B3Q00122Q00882Q00015Q0086000200010010E1008500C8008600128D008600FC3Q00102Q008500C9008600302Q008500CA00CB00202Q00860010006D00102Q008500BE008600122Q0086002Q012Q00102Q008500BF008600068201860060000100012Q0090012Q00103Q0010E8008500C100864Q00830085000200102Q001200FE008300122Q00830002012Q00202Q0084000800C64Q00863Q000700122Q00870003012Q00102Q008600BC00874Q008700023Q00122Q00880004012Q001243008900684Q00050087000200010010E1008600C8008700128D0087001D3Q00102Q008600C9008700302Q008600CA00CF00202Q00870010006B00102Q008600BE008700122Q00870005012Q00102Q008600BF008700068201870061000100012Q0090012Q00103Q00106B008600C100874Q0084008600024Q00120083008400122Q00830006012Q00202Q0084000800C64Q00863Q000700122Q00870007012Q00102Q008600BC00874Q008700023Q00122Q0088003B3Q001243008900454Q00050087000200010010E1008600C8008700128D0087001D3Q00102Q008600C9008700302Q008600CA00CF00202Q00870010006C00102Q008600BE008700122Q00870008012Q00102Q008600BF008700068201870062000100012Q0090012Q00103Q0010E1008600C100872Q00440084008600022Q007B0012008300840020180183000800B800124300850009013Q00260183008500010012430083000A012Q0020180184000800DD2Q006D01863Q00060012430087000B012Q0010E1008600BC00872Q0034008700383Q0012430088003B3Q00067A008800E40301008700044F3Q00E40301000633018700E70301003800044F3Q00E703012Q006D018700013Q0012430088000C013Q00050087000100010010E1008600DF00872Q00E000875Q00102Q008600E000874Q008700013Q00102Q008600E1008700122Q0087000D012Q00102Q008600BF008700068201870063000100052Q0090012Q00104Q0090012Q00384Q0090012Q00114Q0090012Q00124Q0090012Q00543Q0010E1008600C100872Q00440084008600022Q007B0012008300840012430083000E012Q0020180184000800E4001243008600E53Q00204D0187001000172Q0034008700873Q0012430088003B3Q00067A008800060401008700044F3Q00060401001269018700803Q0020F60087008700E600202Q00880010001700122Q008900E76Q00870089000200062Q008700070401000100044F3Q000704010012430087000F013Q00ED0086008600872Q00440084008600022Q007B00120083008400124300830010012Q0020180184000800E400124300860011013Q00440084008600022Q007B0012008300840020180183000800B800124300850012013Q002601830085000100124300830013012Q0020240084000800BB4Q00863Q000400122Q00870014012Q00102Q008600BC00874Q008700013Q00102Q008600BE008700122Q00870015012Q00102Q008600BF008700068201870064000100012Q0090012Q00103Q001007008600C100874Q0084008600024Q00120083008400122Q00830016012Q00202Q0084000800E400122Q00860017015Q0084008600024Q00120083008400202Q0083000800D14Q00853Q000200124300860018012Q0010E1008500BC008600068201860065000100032Q0090012Q00104Q0090012Q000A4Q0090012Q00123Q001045018500C100864Q00830085000100122Q00830019012Q00202Q0084000800C64Q00863Q000600122Q0087001A012Q00102Q008600BC00874Q008700023Q00122Q008800FA3Q00122Q0089001F4Q00050087000200010010E1008600C80087001266018700FA3Q00102Q008600C9008700202Q00870010001C00102Q008600BE008700122Q0087001B012Q00102Q008600BF008700068201870066000100012Q0090012Q00103Q00106B008600C100874Q0084008600024Q00120083008400122Q0083001C012Q00202Q0084000800C64Q00863Q000600122Q0087001D012Q00102Q008600BC00874Q008700023Q00122Q0088003B3Q001243008900454Q00050087000200010010E1008600C800870012660187001D3Q00102Q008600C9008700202Q00870010001E00102Q008600BE008700122Q0087001E012Q00102Q008600BF008700068201870067000100012Q0090012Q00103Q00106B008600C100874Q0084008600024Q00120083008400122Q0083001F012Q00202Q0084000800C64Q00863Q000600122Q00870020012Q00102Q008600BC00874Q008700023Q00122Q0088003B3Q001243008900684Q00050087000200010010E1008600C800870012660187000B3Q00102Q008600C9008700202Q00870010002200102Q008600BE008700122Q00870021012Q00102Q008600BF008700068201870068000100012Q0090012Q00103Q00106B008600C100874Q0084008600024Q00120083008400122Q00830022012Q00202Q0084000800C64Q00863Q000600122Q00870023012Q00102Q008600BC00874Q008700023Q00122Q0088003B3Q001243008900484Q00050087000200010010E1008600C800870012660187001F3Q00102Q008600C9008700202Q00870010002000102Q008600BE008700122Q00870024012Q00102Q008600BF008700068201870069000100012Q0090012Q00103Q00100F008600C100874Q0084008600024Q00120083008400202Q0083000800D14Q00853Q000200122Q00860025012Q00102Q008500BC00860006820186006A000100042Q0090012Q00104Q0090012Q00124Q0090012Q00114Q0090012Q000A3Q0010E1008500C100862Q002601830085000100124300830026012Q0020180184000800DD2Q006D01863Q000600124300870027012Q0010E1008600BC00872Q0034008700393Q0012430088003B3Q00067A008800990401008700044F3Q009904010006330187009C0401003900044F3Q009C04012Q006D018700013Q00124300880028013Q00050087000100010010E1008600DF00872Q00E000875Q00102Q008600E000874Q008700013Q00102Q008600E1008700122Q00870029012Q00102Q008600BF00870006820187006B000100052Q0090012Q00104Q0090012Q00394Q0090012Q00114Q0090012Q00124Q0090012Q00633Q0010E1008600C100872Q00440084008600022Q007B0012008300840012430083002A012Q0020180184000800E40012430086002B012Q00204D0187001000182Q0034008700873Q0012430088003B3Q00067A008800BB0401008700044F3Q00BB0401001269018700803Q0020F60087008700E600202Q00880010001800122Q008900E76Q00870089000200062Q008700BC0401000100044F3Q00BC04010012430087000F013Q00ED0086008600872Q00440084008600022Q007B0012008300840020180183000800D12Q006D01853Q00020012430086002C012Q0010E1008500BC00860006820186006C000100052Q0090012Q00104Q0090012Q00114Q0090012Q00124Q0090012Q00634Q0090012Q000A3Q0010F9008500C100864Q00830085000100122Q0083002D012Q00202Q0084000800BB4Q00863Q000400122Q0087002E012Q00102Q008600BC008700202Q00870010005F00102Q008600BE008700122Q0087002F012Q0010E1008600BF00870006820187006D000100032Q0090012Q00104Q0090012Q00114Q0090012Q00633Q00105A018600C100874Q0084008600024Q00120083008400122Q00830030012Q00202Q0084000800E400122Q00860031015Q0084008600024Q00120083008400122Q00830032012Q00202Q0084000800BB2Q006D01863Q000400126601870033012Q00102Q008600BC008700202Q00870010006A00102Q008600BE008700122Q00870034012Q00102Q008600BF00870006820187006E000100012Q0090012Q00103Q0010E1008600C100872Q00440084008600022Q007B0012008300840020180183000800B800124300850035013Q00260183008500010006820183006F000100012Q0090012Q00383Q00068201840070000100012Q0090012Q00393Q00068201850071000100022Q0090012Q00124Q0090012Q00103Q00068201860072000100052Q0090012Q00684Q0090012Q00674Q0090012Q00114Q0090012Q00854Q0090012Q00633Q00068201870073000100052Q0090012Q00684Q0090012Q00674Q0090012Q00114Q0090012Q00854Q0090012Q00633Q00124300880036012Q0020D00089000800DD4Q008B3Q000600122Q008C0037012Q00102Q008B00BC008C4Q008C00836Q008C0001000200102Q008B00DF008C4Q008C00013Q00122Q008D0038015Q008C000100010010E1008B00E0008C2Q0092018C5Q00102Q008B00E1008C00122Q008C0039012Q00102Q008B00BF008C4Q008C00863Q00122Q008D001F6Q008C0002000200102Q008B00C1008C4Q0089008B00024Q0012008800890012430088003A012Q0020D00089000800DD4Q008B3Q000600122Q008C003B012Q00102Q008B00BC008C4Q008C00846Q008C0001000200102Q008B00DF008C4Q008C00013Q00122Q008D0038015Q008C000100010010E1008B00E0008C2Q0092018C00013Q00102Q008B00E1008C00122Q008C003C012Q00102Q008B00BF008C4Q008C00873Q00122Q008D001F6Q008C0002000200102Q008B00C1008C4Q0089008B00024Q0012008800890012430088003D012Q0020960189000800E400122Q008B003E015Q0089008B00024Q00120088008900122Q0088003F012Q00202Q0089000800DD4Q008B3Q000600122Q008C0040012Q00102Q008B00BC008C4Q008C00834Q0003008C000100020010E1008B00DF008C2Q006D018C00013Q001243008D0038013Q0005008C000100010010E1008B00E0008C2Q0092018C5Q00102Q008B00E1008C00122Q008C0041012Q00102Q008B00BF008C4Q008C00863Q00122Q008D0042015Q008C0002000200102Q008B00C1008C4Q0089008B00024Q00120088008900124300880043012Q0020D00089000800DD4Q008B3Q000600122Q008C0044012Q00102Q008B00BC008C4Q008C00846Q008C0001000200102Q008B00DF008C4Q008C00013Q00122Q008D0038015Q008C000100010010E1008B00E0008C2Q0092018C00013Q00102Q008B00E1008C00122Q008C0045012Q00102Q008B00BF008C4Q008C00873Q00122Q008D0042015Q008C0002000200102Q008B00C1008C4Q0089008B00024Q00120088008900124300880046012Q0020960189000800E400122Q008B003E015Q0089008B00024Q00120088008900122Q00880047012Q00202Q0089000800DD4Q008B3Q000600122Q008C0048012Q00102Q008B00BC008C4Q008C00834Q0003008C000100020010E1008B00DF008C2Q006D018C00013Q001243008D0038013Q0005008C000100010010E1008B00E0008C2Q0092018C5Q00102Q008B00E1008C00122Q008C0049012Q00102Q008B00BF008C4Q008C00863Q00122Q008D007D6Q008C0002000200102Q008B00C1008C4Q0089008B00024Q0012008800890012430088004A012Q0020D00089000800DD4Q008B3Q000600122Q008C004B012Q00102Q008B00BC008C4Q008C00846Q008C0001000200102Q008B00DF008C4Q008C00013Q00122Q008D0038015Q008C000100010010E1008B00E0008C2Q0092018C00013Q00102Q008B00E1008C00122Q008C004C012Q00102Q008B00BF008C4Q008C00873Q00122Q008D007D6Q008C0002000200102Q008B00C1008C4Q0089008B00024Q0012008800890012430088004D012Q0020D40089000800E400122Q008B003E015Q0089008B00024Q00120088008900202Q0088000800D14Q008A3Q000200122Q008B004E012Q00102Q008A00BC008B000682018B0074000100062Q0090012Q00674Q0090012Q00124Q0090012Q00114Q0090012Q00854Q0090012Q00634Q0090012Q000A3Q00108B008A00C1008B4Q0088008A000100202Q0088000800D14Q008A3Q000200122Q008B004F012Q00102Q008A00BC008B000682018B0075000100082Q0090012Q000E4Q0090012Q00684Q0090012Q00674Q0090012Q00124Q0090012Q000A4Q0090012Q00114Q0090012Q00854Q0090012Q00633Q001066008A00C1008B4Q0088008A00014Q00883Q000500122Q00890050015Q008A00063Q00122Q008B0051012Q00122Q008C0052012Q0012DA008D0053012Q00122Q008E0054012Q00122Q008F0055012Q00122Q00900056015Q008A000600012Q007B00880089008A00124300890057013Q006D018A00053Q001243008B0051012Q0012DA008C0052012Q00122Q008D0053012Q00122Q008E0054012Q00122Q008F0055015Q008A000500012Q007B00880089008A00124300890058013Q0072018A00033Q00122Q008B0059012Q00122Q008C005A012Q00122Q008D005B015Q008A000300012Q007B00880089008A0012430089005C013Q006D018A00043Q0012DA008B005D012Q00122Q008C005E012Q00122Q008D005F012Q00122Q008E0060015Q008A000400012Q007B00880089008A00124300890061013Q006D018A6Q007B00880089008A00124300890062012Q002018018A000800DD2Q006D018C3Q0006001243008D0063012Q0010E1008C00BC008D2Q006D018D00053Q001243008E0050012Q0012DA008F0057012Q00122Q00900058012Q00122Q0091005C012Q00122Q00920061015Q008D000500010010E1008C00DF008D2Q00E0008D5Q00102Q008C00E0008D4Q008D5Q00102Q008C00E1008D00122Q008D0064012Q00102Q008C00BF008D000682018D0076000100082Q0090012Q00884Q0090012Q000E4Q0090012Q00394Q0090012Q00104Q0090012Q000A4Q0090012Q00124Q0090012Q00114Q0090012Q00633Q0010D6008C00C1008D4Q008A008C00024Q00120089008A00122Q00890065012Q00202Q008A000800BB4Q008C3Q000400122Q008D0066012Q00102Q008C00BC008D00202Q008D0010005A00102Q008C00BE008D001243008D0067012Q0010E1008C00BF008D000682018D0077000100012Q0090012Q00103Q0010D6008C00C1008D4Q008A008C00024Q00120089008A00122Q00890068012Q00202Q008A000800BB4Q008C3Q000400122Q008D0069012Q00102Q008C00BC008D00202Q008D0010005D00102Q008C00BE008D001243008D006A012Q0010E1008C00BF008D000682018D0078000100012Q0090012Q00103Q0010D6008C00C1008D4Q008A008C00024Q00120089008A00122Q0089006B012Q00202Q008A000800BB4Q008C3Q000400122Q008D006C012Q00102Q008C00BC008D00202Q008D0010005E00102Q008C00BE008D001243008D006D012Q0010E1008C00BF008D000682018D0079000100022Q0090012Q00104Q0090012Q00113Q0010E1008C00C1008D2Q0044008A008C00022Q007B00120089008A001243008B006E013Q00B100890008008B2Q006D018B3Q0002001243008C006F012Q001243008D0070013Q007B008B008C008D001243008C0071012Q001243008D0072013Q007B008B008C008D2Q00260189008B0001001269018900023Q00204D0189008900030010E1008900B00010001269018900023Q00204D018900890003001215008A0073015Q0089008A000F00122Q008900023Q00202Q00890089000300122Q008A0074013Q007B0089008A0012001269018900023Q00204D018900890003001243008A0075012Q000682018B007A000100062Q0090012Q00104Q0090012Q00804Q0090012Q00124Q0090012Q000F4Q0090012Q00114Q0090012Q00164Q007B0089008A008B001269018900023Q00204D018900890003001243008A0076012Q000682018B007B000100062Q0090012Q00104Q0090012Q00204Q0090012Q00174Q0090012Q00804Q0090012Q00554Q0090012Q00124Q00CD0089008A008B00122Q00890077012Q00122Q008A0077015Q008A0007008A00062Q008A00540601000100044F3Q005406012Q006D018A6Q007B00070089008A001269018900803Q001243008A0078013Q00C000890089008A001243008A0077013Q00C0008A0007008A2Q0090018B007C4Q00260189008B00010012690189007F3Q001243008A0079013Q00C0008A0007008A2Q00310089000200020026DF008900690601008000044F3Q00690601001269018900803Q001243008A0078013Q00C000890089008A001243008A0079013Q00C0008A0007008A2Q0090018B007C4Q00260189008B00012Q00900189000A4Q006D018A3Q0003001243008B006F012Q001243008C007A013Q007B008A008B008C001243008B0071012Q001243008C007B013Q007B008A008B008C001243008B007C012Q001243008C0042013Q007B008A008B008C2Q007B018900020001001269018900D53Q001243008A007D013Q007B0189000200012Q0064012Q00013Q007C3Q00013Q00030B3Q004C6F63616C506C6179657200094Q0099016Q00060D012Q00060001000100044F3Q000600012Q0099012Q00013Q00204D014Q00012Q0097017Q0099017Q00E23Q00024Q0064012Q00017Q00023Q0003083Q005261796669656C6403063Q004E6F7469667901114Q00992Q015Q00060D2Q0100080001000100044F3Q000800012Q00992Q0100013Q0006082Q01000800013Q00044F3Q000800012Q00992Q0100013Q00204D2Q01000100010006082Q01001000013Q00044F3Q0010000100204D0102000100020006080102001000013Q00044F3Q001000010020180102000100022Q009001046Q00260102000400012Q0064012Q00017Q00063Q0003053Q005574696C7303073Q00476574522Q6F7403043Q007479706503083Q0066756E6374696F6E030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727401184Q00992Q015Q0006082Q01000500013Q00044F3Q000500012Q00992Q015Q00204D2Q01000100010006B8000200080001000100044F3Q0008000100204D010200010002001269010300034Q0090010400024Q00310003000200020026DF000300110001000400044F3Q001100012Q0090010300024Q009001046Q002C000300044Q002101035Q0006B80003001600013Q00044F3Q0016000100201801033Q0005001243000500064Q00440003000500022Q00E2000300024Q0064012Q00017Q00023Q0003093Q00436F2Q6E6563746564010001093Q0006B80001000700013Q00044F3Q0007000100204D2Q013Q00010026DF000100060001000200044F3Q000600012Q00EF00016Q008B2Q0100014Q00E2000100024Q0064012Q00017Q00143Q00030B3Q005B412Q6C2041726561735D030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007072696E74032A3Q005B466F726765204D696E696E675D2Q20576F726B73706163652E526F636B73206E6F7420666F756E642103103Q00284E6F20417265617320466F756E642903053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C03053Q007461626C6503063Q00696E7365727403043Q004E616D6503043Q00736F727403063Q00697061697273028Q0003063Q00737472696E6703063Q00666F726D617403383Q005B466F726765204D696E696E675D2Q20466F756E64202564206D696E696E6720617265617320696E20576F726B73706163652E526F636B7300464Q006D012Q00013Q001243000100014Q00053Q000100012Q00992Q015Q0020182Q0100010002001243000300034Q004400010003000200060D2Q0100100001000100044F3Q00100001001269010200043Q001259010300056Q0002000200014Q000200013Q00122Q000300066Q0002000100012Q00E2000200024Q006D01025Q0012F0000300073Q00202Q0004000100084Q000400056Q00033Q000500044Q00250001002018010800070009001243000A000A4Q00440008000A000200060D010800200001000100044F3Q00200001002018010800070009001243000A000B4Q00440008000A00020006080108002500013Q00044F3Q002500010012690108000C3Q00204D01080008000D2Q0090010900023Q00204D010A0007000E2Q00260108000A00010006AA000300160001000200044F3Q001600010012690103000C3Q00206F01030003000F4Q000400026Q00030002000100122Q000300106Q000400026Q00030002000500044Q003400010012690108000C3Q00204D01080008000D2Q009001096Q0090010A00074Q00260108000A00010006AA0003002F0001000200044F3Q002F00012Q0034000300023Q0026DF0003003D0001001100044F3Q003D00012Q006D010300013Q001243000400064Q00050003000100012Q00E2000300023Q001269010300043Q001257010400123Q00202Q00040004001300122Q000500146Q000600026Q000400066Q00033Q00016Q00028Q00017Q00033Q0003043Q007469636B028Q00026Q00F03F01153Q0012692Q0100014Q000300010001000200060D012Q000E0001000100044F3Q000E00012Q009901026Q0034000200023Q000ED50002000E0001000200044F3Q000E00012Q0099010200014Q00790102000100020026240102000E0001000300044F3Q000E00012Q009901026Q00E2000200024Q0099010200024Q003C0002000100024Q00028Q000100016Q00028Q000200028Q00017Q000B3Q00030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03043Q004E616D652Q0103053Q007461626C6503063Q00696E7365727403043Q00736F727401354Q009100018Q00025Q00202Q00020002000100122Q000400026Q00020004000200062Q000200090001000100044F3Q000900012Q006D01036Q00E2000300023Q0020180103000200012Q009001056Q00440003000500020006080103002300013Q00044F3Q00230001001269010400033Q0020180105000300042Q0041000500064Q002201043Q000600044F3Q00210001001269010900033Q002018010A000800042Q0041000A000B4Q002201093Q000B00044F3Q001F0001002018010E000D0005001243001000064Q0044000E00100002000608010E001F00013Q00044F3Q001F000100204D010E000D00070020120001000E00080006AA000900180001000200044F3Q001800010006AA000400130001000200044F3Q001300012Q006D01045Q001269010500034Q0090010600014Q001C00050002000700044F3Q002D0001001269010900093Q00204D01090009000A2Q0090010A00044Q0090010B00084Q00260109000B00010006AA000500280001000100044F3Q00280001001269010500093Q0020A100050005000B4Q000600046Q0005000200014Q000400028Q00017Q000C3Q00030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C03043Q004E616D652Q0103053Q007461626C6503063Q00696E7365727403043Q00736F727400414Q00919Q0000015Q00202Q00010001000100122Q000300026Q00010003000200062Q000100090001000100044F3Q000900012Q006D01026Q00E2000200023Q001269010200033Q0020180103000100042Q0041000300044Q002201023Q000400044F3Q002D0001002018010700060005001243000900064Q004400070009000200060D010700180001000100044F3Q00180001002018010700060005001243000900074Q00440007000900020006080107002D00013Q00044F3Q002D0001001269010700033Q0020180108000600042Q0041000800094Q002201073Q000900044F3Q002B0001001269010C00033Q002018010D000B00042Q0041000D000E4Q0022010C3Q000E00044F3Q00290001002018011100100005001243001300074Q00440011001300020006080111002900013Q00044F3Q0029000100204D0111001000080020123Q001100090006AA000C00220001000200044F3Q002200010006AA0007001D0001000200044F3Q001D00010006AA0002000E0001000200044F3Q000E00012Q006D01025Q001269010300034Q009001046Q001C00030002000500044F3Q003900010012690107000A3Q00204D01070007000B2Q0090010800024Q0090010900064Q00260107000900010006AA000300340001000100044F3Q003400010012690103000A3Q0020A100030003000C4Q000400026Q0003000200014Q000200028Q00017Q00033Q0003043Q007469636B028Q00026Q00F03F011F3Q0012692Q0100014Q00030001000100022Q009901025Q0006080102000700013Q00044F3Q000700012Q006D01026Q0097010200013Q00060D012Q00160001000100044F3Q001600012Q009901025Q00060D010200160001000100044F3Q001600012Q0099010200014Q0034000200023Q000ED5000200160001000200044F3Q001600012Q0099010200024Q0079010200010002002624010200160001000300044F3Q001600012Q0099010200014Q00E2000200024Q0099010200034Q00400002000100024Q000200016Q000100026Q00028Q00028Q000200016Q000200028Q00017Q00023Q002Q033Q0049734103063Q0055494261736500064Q0058016Q00206Q000100122Q000200028Q00029Q008Q00017Q00023Q002Q033Q00497341030B3Q005549436F6D706F6E656E7400064Q0058016Q00206Q000100122Q000200028Q00029Q008Q00017Q00043Q0003043Q004E616D652Q033Q0049734103063Q00554942617365030B3Q005549436F6D706F6E656E7402233Q00060D012Q00040001000100044F3Q000400012Q008B010200014Q00E2000200023Q0006082Q01000C00013Q00044F3Q000C000100204D01023Q00012Q00C00002000100020006080102000C00013Q00044F3Q000C00012Q008B010200014Q00E2000200024Q009901025Q0006080102001600013Q00044F3Q0016000100201801023Q0002001243000400034Q00440002000400020006080102001600013Q00044F3Q001600012Q008B010200014Q00E2000200024Q0099010200013Q0006080102002000013Q00044F3Q0020000100201801023Q0002001243000400044Q00440002000400020006080102002000013Q00044F3Q002000012Q008B010200014Q00E2000200024Q008B01026Q00E2000200024Q0064012Q00017Q001E3Q00030B3Q004C6F63616C506C6179657203053Q007063612Q6C030C3Q005549477269644C61796F75742Q01030C3Q0055494C6973744C61796F757403093Q00554950612Q64696E6703173Q005549417370656374526174696F436F6E73747261696E7403073Q0055495363616C6503083Q0055495374726F6B6503083Q005549436F726E657203073Q005468655065616B030D3Q00546865205065616B204C69737403043Q005065616B030E3Q0046696E6446697273744368696C6403053Q007461626C6503043Q00736F727403053Q007072696E7403203Q005B466F726765204D696E696E675D204765744F726573466F7249736C616E642803093Q00293A20466F756E642003113Q00206F72657320766961206D612Q70696E6703053Q00204C69737403043Q006773756203063Q0049736C616E64034Q0003043Q004361766503053Q0053746172742Q033Q0052656403063Q0069706169727303103Q00206F72657320286D6174636865643A2003013Q002901714Q006D2Q016Q009901025Q00204D010200020001001269010300023Q00068201043Q000100012Q0090012Q00024Q001C0003000200040006080103000B00013Q00044F3Q000B000100060D0104000D0001000100044F3Q000D00012Q006D01056Q00E2000500024Q006D01053Q000700303801050003000400302Q00050005000400302Q00050006000400302Q00050007000400302Q00050008000400302Q00050009000400302Q0005000A000400068201060001000100032Q0099012Q00014Q0090012Q00054Q0090012Q00014Q001400073Q000200302Q0007000B000C00302Q0007000D000C4Q000800073Q00062Q0008003400013Q00044F3Q0034000100201801090004000E2Q0090010B00084Q00440009000B00020006080109003400013Q00044F3Q003400012Q0090010A00064Q0090010B00094Q007B010A00020001001269010A000F3Q00204D010A000A00102Q0090010B00014Q007B010A00020001001269010A00113Q001243000B00124Q0090010C5Q001243000D00134Q0034000E00013Q001243000F00144Q00ED000B000B000F2Q007B010A000200012Q00E2000100024Q006D010900064Q0089000A5Q00122Q000B00156Q000A000A000B4Q000B5Q00202Q000C3Q001600122Q000E00173Q00122Q000F00186Q000C000F000200122Q000D00156Q000C000C000D00202Q000D3Q001600122Q000F00193Q00122Q001000186Q000D0010000200122Q000E00156Q000D000D000E00202Q000E3Q001600122Q0010001A3Q00122Q001100186Q000E0011000200122Q000F00156Q000E000E000F00202Q000F3Q001600122Q0011001B3Q00122Q001200186Q000F0012000200122Q001000156Q000F000F00104Q000900060001001269010A001C4Q0090010B00094Q001C000A0002000C00044F3Q00690001002018010F0004000E2Q00900111000E4Q0044000F00110002000608010F006900013Q00044F3Q006900012Q0090011000064Q00700011000F6Q00100002000100122Q001000113Q00122Q001100126Q00125Q00122Q001300136Q001400013Q00122Q0015001D6Q0016000E3Q00122Q0017001E6Q0011001100174Q00100002000100044Q006B00010006AA000A00560001000200044F3Q00560001001269010A000F3Q0020A1000A000A00104Q000B00016Q000A000200014Q000100028Q00013Q00023Q00073Q0003093Q00506C6179657247756903043Q004D656E7503053Q004672616D6503053Q004D656E757303053Q00496E64657803053Q00506167657303043Q004F726573000B4Q00107Q00206Q000100206Q000200206Q000300206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00053Q0003053Q007061697273030B3Q004765744368696C6472656E03053Q007461626C6503063Q00696E7365727403043Q004E616D6501133Q0012F0000100013Q00202Q00023Q00024Q000200036Q00013Q000300044Q001000012Q009901066Q0090010700054Q0099010800014Q004400060008000200060D010600100001000100044F3Q00100001001269010600033Q00204D0106000600042Q0099010700023Q00204D0108000500052Q00260106000800010006AA000100050001000200044F3Q000500012Q0064012Q00017Q00163Q00030B3Q004C6F63616C506C6179657203053Q007063612Q6C030C3Q005549477269644C61796F75742Q01030C3Q0055494C6973744C61796F757403093Q00554950612Q64696E6703173Q005549417370656374526174696F436F6E73747261696E7403073Q0055495363616C6503083Q0055495374726F6B6503083Q005549436F726E657203053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D652Q033Q00737562026Q0014C003053Q00204C69737403053Q007461626C6503063Q00696E7365727403043Q00736F727403053Q007072696E7403253Q005B466F726765204D696E696E675D20476574412Q6C4F726554797065733A20466F756E6420031B3Q0020756E69717565206F7265732066726F6D20506C6179657247756900474Q002B019Q00018Q00025Q00202Q00020002000100122Q000300023Q00068201043Q000100012Q0090012Q00024Q001C0003000200040006080103000C00013Q00044F3Q000C000100060D0104000E0001000100044F3Q000E00012Q006D01056Q00E2000500024Q006D01053Q000700303801050003000400302Q00050005000400302Q00050006000400302Q00050007000400302Q00050008000400302Q00050009000400302Q0005000A00040012F00006000B3Q00202Q00070004000C4Q000700086Q00063Q000800044Q0039000100204D010B000A000D002018010B000B000E001243000D000F4Q0044000B000D00020026DF000B00390001001000044F3Q00390001001269010B000B3Q002018010C000A000C2Q0041000C000D4Q0022010B3Q000D00044F3Q003700012Q0099011000014Q00900111000F4Q0090011200054Q004400100012000200060D011000370001000100044F3Q0037000100204D0110000F000D2Q00C000100001001000060D011000370001000100044F3Q0037000100204D0110000F000D002012000100100004001269011000113Q00204D0110001000122Q009001115Q00204D0112000F000D2Q00260110001200010006AA000B00260001000200044F3Q002600010006AA0006001B0001000200044F3Q001B0001001269010600113Q0020340106000600134Q00078Q00060002000100122Q000600143Q00122Q000700156Q00085Q00122Q000900166Q0007000700094Q0006000200016Q00028Q00013Q00013Q00073Q0003093Q00506C6179657247756903043Q004D656E7503053Q004672616D6503053Q004D656E757303053Q00496E64657803053Q00506167657303043Q004F726573000B4Q00107Q00206Q000100206Q000200206Q000300206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00033Q0003043Q007469636B028Q00026Q00F03F01153Q0012692Q0100014Q000300010001000200060D012Q000E0001000100044F3Q000E00012Q009901026Q0034000200023Q000ED50002000E0001000200044F3Q000E00012Q0099010200014Q00790102000100020026240102000E0001000300044F3Q000E00012Q009901026Q00E2000200024Q0099010200024Q003C0002000100024Q00028Q000100016Q00028Q000200028Q00017Q000B3Q00030B3Q004C6F63616C506C6179657203053Q007063612Q6C03053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D652Q033Q00737562026Q0014C003053Q00204C69737403053Q007461626C6503063Q00696E7365727403043Q00736F727400254Q006D017Q00992Q015Q00204D2Q0100010001001269010200023Q00068201033Q000100012Q0090012Q00014Q001C0002000200030006080102000B00013Q00044F3Q000B000100060D0103000D0001000100044F3Q000D00012Q006D01046Q00E2000400023Q001269010400033Q0020180105000300042Q0041000500064Q002201043Q000600044F3Q001D000100204D010900080005002018010900090006001243000B00074Q00440009000B00020026DF0009001D0001000800044F3Q001D0001001269010900093Q00204D01090009000A2Q0090010A5Q00204D010B000800052Q00260109000B00010006AA000400120001000200044F3Q00120001001269010400093Q0020A100040004000B4Q00058Q0004000200016Q00028Q00013Q00013Q00073Q0003093Q00506C6179657247756903043Q004D656E7503053Q004672616D6503053Q004D656E757303053Q00496E64657803053Q00506167657303043Q004F726573000B4Q00107Q00206Q000100206Q000200206Q000300206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00103Q00026Q005940026Q003440026Q004440026Q004E40026Q00544003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03063Q00697061697273030E3Q0046696E6446697273744368696C6403083Q00746F737472696E6703083Q004261736550617274030C3Q005472616E73706172656E637902CD5QCCEC3F2Q033Q004F7265013E3Q00060D012Q00040001000100044F3Q00040001001243000100014Q00E2000100024Q006D2Q0100053Q001243000200023Q0012DA000300033Q00122Q000400043Q00122Q000500053Q00122Q000600016Q0001000500012Q001A010200023Q0012F0000300063Q00202Q00043Q00074Q000400056Q00033Q000500044Q00180001002018010800070008001243000A00094Q00440008000A00020006080108001800013Q00044F3Q001800012Q0090010200073Q00044F3Q001A00010006AA000300110001000200044F3Q0011000100060D0102001D0001000100044F3Q001D00012Q009001025Q0012690103000A4Q0090010400014Q001C00030002000500044F3Q0031000100201801080002000B0012D2000A000C6Q000B00076Q000A000B6Q00083Q000200062Q0008003100013Q00044F3Q00310001002018010900080008001243000B000D4Q00440009000B00020006080109003100013Q00044F3Q0031000100204D01090008000E002624010900310001000F00044F3Q003100012Q00E2000700023Q0006AA000300210001000200044F3Q0021000100201801030002000B001243000500104Q008B010600014Q00440003000600020006080103003B00013Q00044F3Q003B0001001243000400034Q00E2000400023Q001243000400014Q00E2000400024Q0064012Q00017Q000C3Q0003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C030E3Q0046696E6446697273744368696C6403063Q00726F636B485003093Q00546578744C6162656C03043Q005465787403083Q00746F6E756D62657203053Q006D617463682Q033Q0025642B028Q00012E3Q00060D012Q00040001000100044F3Q000400012Q001A2Q0100014Q00E2000100024Q001A2Q0100013Q0012F0000200013Q00202Q00033Q00024Q000300046Q00023Q000400044Q00110001002018010700060003001243000900044Q00440007000900020006080107001100013Q00044F3Q001100012Q00902Q0100063Q00044F3Q001300010006AA0002000A0001000200044F3Q000A000100060D2Q0100160001000100044F3Q001600012Q00902Q015Q002018010200010005001243000400064Q008B010500014Q00440002000500020006080102002B00013Q00044F3Q002B0001002018010300020003001243000500074Q00440003000500020006080103002B00013Q00044F3Q002B000100204D01030002000800122B000400093Q00202Q00050003000A00122Q0007000B6Q000500076Q00043Q000200062Q0005002A0001000400044F3Q002A00010012430005000C4Q00E2000500024Q001A010300034Q00E2000300024Q0064012Q00017Q00073Q0003053Q007061697273030E3Q0047657444657363656E64616E747303043Q004E616D652Q033Q004F72652Q033Q0049734103053Q004D6F64656C030C3Q00476574412Q74726962757465011A3Q00060D012Q00040001000100044F3Q000400012Q001A2Q0100014Q00E2000100023Q0012692Q0100013Q00201801023Q00022Q0041000200034Q00222Q013Q000300044F3Q0015000100204D0106000500030026DF000600150001000400044F3Q00150001002018010600050005001243000800064Q00440006000800020006080106001500013Q00044F3Q00150001002018010600050007001243000800044Q002C000600084Q002101065Q0006AA000100090001000200044F3Q000900012Q001A2Q0100014Q00E2000100024Q0064012Q00017Q00063Q0003083Q00746F737472696E67034Q0003043Q006773756203043Q005B25635D03053Q005B802DFF5D03013Q003F01113Q0012692Q0100013Q0006330102000400013Q00044F3Q00040001001243000200024Q00310001000200022Q0011012Q00013Q00202Q00013Q000300122Q000300043Q00122Q000400026Q00010004000200202Q00010001000300122Q000300053Q00122Q000400066Q0001000400026Q00014Q00E23Q00024Q0064012Q00017Q00033Q0003093Q0044656275674D6F646503053Q007072696E74030F3Q005B466F726765204D696E696E675D20020E4Q009901025Q00204D01020002000100060D010200060001000100044F3Q000600010006082Q01000D00013Q00044F3Q000D0001001269010200023Q001236000300036Q000400016Q00058Q0004000200024Q0003000300044Q0002000200012Q0064012Q00017Q00023Q0003043Q007469636B028Q0002113Q00122F010200016Q0002000100024Q00038Q000300033Q00062Q000300070001000100044F3Q00070001001243000300024Q007901040002000300067A0004000C0001000100044F3Q000C00012Q008B010400014Q00E2000400024Q009901046Q007B00043Q00022Q008B01046Q00E2000400024Q0064012Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403063Q004C6976696E6703043Q004E616D6500134Q0099017Q00033Q0001000200060D012Q00060001000100044F3Q000600012Q001A2Q0100014Q00E2000100024Q00992Q0100013Q0020182Q0100010001001243000300024Q00440001000300020006082Q01001000013Q00044F3Q0010000100201801020001000100204D01043Q00032Q002C000200044Q002101026Q001A010200024Q00E2000200024Q0064012Q00017Q00073Q0003043Q006D61746803053Q00666C2Q6F72025Q0020AC40026Q004E4003063Q00737472696E6703063Q00666F726D6174030E3Q00253032643A253032643A2530326401163Q0012692Q0100013Q00204D2Q010001000200200C01023Q00032Q0031000100020002001269010200013Q00204D01020002000200207600033Q000300200C0103000300042Q0031000200020002001269010300013Q00204D01030003000200207600043Q00042Q0031000300020002001269010400053Q00204D010400040006001243000500074Q0090010600014Q0090010700024Q0090010800034Q002C000400084Q002101046Q0064012Q00017Q00013Q0003013Q005801083Q00204D2Q013Q000100204D01023Q00010006A7000100050001000200044F3Q000500012Q00EF00016Q008B2Q0100014Q00E2000100024Q0064012Q00019Q003Q00094Q008B012Q00014Q0097017Q006D017Q0097012Q00014Q006D017Q0097012Q00024Q006D017Q0097012Q00034Q0064012Q00017Q00073Q0003043Q007469636B029A5Q99C93F030E3Q0046696E6446697273744368696C6403053Q00526F636B73030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637403123Q0044657363656E64616E7452656D6F76696E6700283Q001269012Q00014Q00033Q000100022Q00992Q015Q0006082Q01000B00013Q00044F3Q000B00012Q00992Q0100014Q00792Q013Q00010026242Q01000B0001000200044F3Q000B00012Q00992Q016Q00E2000100024Q0097012Q00014Q00FD000100023Q00202Q00010001000300122Q000300046Q0001000300024Q00018Q00015Q00062Q0001002500013Q00044F3Q002500012Q00992Q0100033Q00060D2Q0100250001000100044F3Q002500012Q008B2Q0100014Q00302Q0100036Q00015Q00202Q00010001000500202Q0001000100064Q000300056Q0001000300024Q000100046Q00015Q00202Q00010001000700202Q0001000100064Q000300056Q0001000300024Q000100064Q00992Q016Q00E2000100024Q0064012Q00017Q00093Q0003043Q007469636B026Q00E03F030E3Q0046696E6446697273744368696C64030D3Q00537061776E4C6F636174696F6E03113Q005361666548656967687444656661756C7403083Q00506F736974696F6E03093Q004D61676E697475646503103Q00537061776E436865636B526164697573030F3Q0053616665486569676874537061776E011D3Q0012692Q0100014Q00030001000100022Q009901026Q0079010200010002002624010200080001000200044F3Q000800012Q0099010200014Q00E2000200024Q00972Q016Q009D010200023Q00202Q00020002000300122Q000400046Q0002000400024Q000300033Q00202Q00030003000500062Q0002001A00013Q00044F3Q001A000100204D0104000200062Q009E00043Q000400202Q0004000400074Q000500033Q00202Q00050005000800062Q0004001A0001000500044F3Q001A00012Q0099010400033Q00204D0103000400092Q0097010300014Q00E2000300024Q0064012Q00017Q00023Q0003063Q00506172656E74030D3Q0043752Q72656E7443616D657261000D4Q0099016Q000608012Q000700013Q00044F3Q000700012Q0099016Q00204D014Q000100060D012Q000A0001000100044F3Q000A00012Q0099012Q00013Q00204D014Q00022Q0097017Q0099017Q00E23Q00024Q0064012Q00017Q000E3Q00030A3Q0043616D6572614D6F646503043Q004E6F6E6503153Q002043616D657261206E6F7420617661696C61626C6503123Q004F726967696E616C43616D65726154797065030A3Q0043616D6572615479706503103Q0043616D657261436F2Q6E656374696F6E030A3Q00446973636F2Q6E6563740003093Q0043616D434672616D6503163Q002043616D657261204D6F646520535441525445443A2003043Q00456E756D030A3Q0053637269707461626C65030D3Q0052656E6465725374652Q70656403073Q00436F2Q6E65637400384Q0099016Q00204D014Q00010026DF3Q00050001000200044F3Q000500012Q0064012Q00014Q0099012Q00014Q00033Q0001000200060D012Q000E0001000100044F3Q000E00012Q00992Q0100023Q001243000200034Q008B010300014Q00262Q01000300012Q0064012Q00014Q00992Q0100033Q00204D2Q010001000400060D2Q0100150001000100044F3Q001500012Q00992Q0100033Q00204D01023Q00050010E10001000400022Q00992Q0100033Q00204D2Q01000100060006082Q01001F00013Q00044F3Q001F00012Q00992Q0100033Q00204D2Q01000100060020182Q01000100072Q007B2Q01000200012Q00992Q0100033Q00306D0001000600082Q00992Q0100033Q00305F0001000900084Q000100023Q00122Q0002000A6Q00035Q00202Q0003000300014Q0002000200034Q00010002000100122Q0001000B3Q00202Q00010001000500202Q00010001000C00104Q000500014Q000100036Q000200043Q00202Q00020002000D00202Q00020002000E00068201043Q000100052Q0099017Q0099012Q00014Q0099012Q00054Q0099012Q00064Q0099012Q00034Q00440002000400020010E10001000600022Q0064012Q00013Q00013Q001A3Q00030A3Q004175746F4D696E696E67030B3Q0043752Q72656E74526F636B03043Q0074797065030D3Q00476574526F636B486974626F7803083Q0066756E6374696F6E030C3Q0043616D657261486569676874030E3Q0043616D65726144697374616E6365030A3Q0043616D65726153696465030A3Q0043616D6572614D6F6465030A3Q004C6F636B54617267657403083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E657703013Q0058028Q0003013Q005A03093Q004D61676E6974756465029A5Q99B93F03043Q00556E6974026Q00F0BF03063Q00434672616D6503063Q006C2Q6F6B4174030A3Q004C2Q6F6B566563746F72030B3Q005269676874566563746F72030B3Q0046697865644F2Q66736574026Q00144000954Q0099016Q00204D014Q000100060D012Q00050001000100044F3Q000500012Q0064012Q00014Q0099012Q00014Q00033Q0001000200060D012Q000A0001000100044F3Q000A00012Q0064012Q00014Q00992Q0100024Q009E2Q01000100024Q000200036Q000300016Q00020002000200062Q000200120001000100044F3Q001200012Q0064012Q00014Q001A010300034Q0099010400043Q00204D0104000400020006080104002100013Q00044F3Q00210001001269010400033Q001269010500044Q00310004000200020026DF000400210001000500044F3Q00210001001269010400044Q0099010500043Q00204D0105000500022Q00310004000200022Q0090010300044Q009901045Q0020FC0004000400064Q00055Q00202Q0005000500074Q00065Q00202Q0006000600084Q00075Q00202Q00070007000900262Q000700720001000A00044F3Q007200010006080103005B00013Q00044F3Q005B000100204D01070002000B00206F00080003000B4Q00090008000700122Q000A000C3Q00202Q000A000A000D00202Q000B0009000E00122Q000C000F3Q00202Q000D000900104Q000A000D000200202Q000B000A0011000E2Q0012003C0001000B00044F3Q003C000100204D010B000A001300060D010B00420001000100044F3Q00420001001269010B000C3Q00204D010B000B000D001243000C000F3Q001243000D000F3Q001243000E00144Q0044000B000E0002001269010C000C3Q002070010C000C000D00202Q000D000B001000122Q000E000F3Q00202Q000F000B000E4Q000F000F6Q000C000F00024Q000D000B00054Q000D0007000D00122Q000E000C3Q00202Q000E000E000D00122Q000F000F6Q001000043Q00122Q0011000F6Q000E001100024Q000D000D000E4Q000E000C00064Q000D000D000E00122Q000E00153Q00202Q000E000E00164Q000F000D6Q001000086Q000E0010000200104Q0015000E00044Q0094000100204D01070002001500200201070007001700202Q00080002001500202Q00080008001800202Q00090002000B4Q000A000700054Q00090009000A00122Q000A000C3Q00202Q000A000A000D00122Q000B000F6Q000C00043Q00122Q000D000F6Q000A000D00024Q00090009000A4Q000A000800064Q00090009000A00122Q000A00153Q00202Q000A000A00164Q000B00093Q00202Q000C0002000B4Q000A000C000200104Q0015000A00044Q009400012Q009901075Q00204D0107000700090026DF000700940001001900044F3Q0094000100204D01070002001500204D01070007001700204D01080002001500204D01080008001800204D01090002000B2Q0068010A000700052Q007901090009000A001269010A000C3Q00204D010A000A000D001243000B000F4Q0090010C00043Q001243000D000F4Q008D010A000D00024Q00090009000A4Q000A000800064Q00090009000A00202Q000A0002000B00122Q000B000C3Q00202Q000B000B000D00122Q000C000F3Q00122Q000D001A3Q00122Q000E000F4Q0044000B000E00022Q0047010A000A000B00122Q000B00153Q00202Q000B000B00164Q000C00096Q000D000A6Q000B000D000200104Q0015000B2Q0064012Q00017Q000A3Q0003103Q0043616D657261436F2Q6E656374696F6E030A3Q00446973636F2Q6E6563740003143Q002043616D657261204D6F64652053544F2Q50454403123Q004F726967696E616C43616D65726154797065030A3Q0043616D6572615479706503153Q002043616D65726120726573746F72656420746F3A2003083Q00746F737472696E6703043Q00456E756D03063Q00437573746F6D00294Q0099016Q00204D014Q0001000608012Q000D00013Q00044F3Q000D00012Q0099016Q00200C5Q000100206Q00026Q000200019Q0000304Q000100036Q00013Q00122Q000100048Q000200012Q0099012Q00024Q00033Q000100022Q00992Q015Q00204D2Q01000100050006082Q01002200013Q00044F3Q00220001000608012Q002200013Q00044F3Q002200012Q00992Q015Q00200F2Q010001000500104Q000600014Q00015Q00302Q0001000500034Q000100013Q00122Q000200073Q00122Q000300083Q00202Q00043Q00064Q0003000200024Q0002000200034Q00010002000100044Q00280001000608012Q002800013Q00044F3Q002800010012692Q0100093Q00204D2Q010001000600204D2Q010001000A0010E13Q000600012Q0064012Q00017Q00073Q0003023Q005F4703053Q00466F726765030B3Q0043616D6572615368616B65030A3Q00497344697361626C656403053Q007063612Q6C03123Q0043616D6572615368616B65526573746F726503063Q00456E61626C65001D3Q001269012Q00013Q00204D014Q0002000608012Q000700013Q00044F3Q00070001001269012Q00013Q00204D014Q000200204D014Q000300060D012Q000A0001000100044F3Q000A00012Q0064012Q00014Q001A2Q0100013Q00204D01023Q00040006080102001400013Q00044F3Q00140001001269010200053Q00204D01033Q00042Q001C0002000200030006080102001400013Q00044F3Q001400012Q00902Q0100034Q009901025Q0010E100020006000100204D01023Q00070006080102001C00013Q00044F3Q001C0001001269010200053Q00204D01033Q00072Q007B0102000200012Q0064012Q00017Q000A3Q0003023Q005F4703053Q00466F726765030B3Q0043616D6572615368616B6503123Q0043616D6572615368616B65526573746F7265002Q0103073Q0044697361626C6503053Q007063612Q6C010003063Q00456E61626C6500223Q001269012Q00013Q00204D014Q0002000608012Q000700013Q00044F3Q00070001001269012Q00013Q00204D014Q000200204D014Q00032Q00992Q015Q00204D2Q01000100042Q009901025Q00306D000200040005000608012Q000F00013Q00044F3Q000F00010026DF000100100001000500044F3Q001000012Q0064012Q00013Q0026DF000100190001000600044F3Q0019000100204D01023Q00070006080102001900013Q00044F3Q00190001001269010200083Q00204D01033Q00072Q007B01020002000100044F3Q002100010026DF000100210001000900044F3Q0021000100204D01023Q000A0006080102002100013Q00044F3Q00210001001269010200083Q00204D01033Q000A2Q007B0102000200012Q0064012Q00017Q000E3Q0003043Q007469636B03043Q0074696D65026Q00144003063Q00686974626F7803063Q00506172656E74030E3Q00497344657363656E64616E744F660003053Q007061697273030E3Q0047657444657363656E64616E747303043Q004E616D6503063Q00486974626F782Q033Q0049734103083Q004261736550617274030D3Q00537061776E4C6F636174696F6E014D3Q00060D012Q00040001000100044F3Q000400012Q001A2Q0100014Q00E2000100024Q00992Q016Q00C0000100013Q0006082Q01001F00013Q00044F3Q001F0001001269010200014Q000300020001000200204D0103000100022Q00790102000200030026240102001F0001000300044F3Q001F000100204D0102000100040006080102001D00013Q00044F3Q001D000100204D01020001000400204D0102000200050006080102001D00013Q00044F3Q001D000100204D0102000100040020180102000200062Q009001046Q00440002000400020006080102001D00013Q00044F3Q001D000100204D0102000100042Q00E2000200024Q009901025Q00201200023Q00072Q001A010200023Q0012F0000300083Q00202Q00043Q00094Q000400056Q00033Q000500044Q002F000100204D01080007000A0026DF0008002F0001000B00044F3Q002F000100201801080007000C001243000A000D4Q00440008000A00020006080108002F00013Q00044F3Q002F00012Q0090010200073Q00044F3Q003100010006AA000300250001000200044F3Q0025000100060D010200440001000100044F3Q00440001001269010300083Q00201801043Q00092Q0041000400054Q002201033Q000500044F3Q0042000100201801080007000C001243000A000D4Q00440008000A00020006080108004200013Q00044F3Q0042000100204D01080007000A0026E5000800420001000E00044F3Q004200012Q0090010200073Q00044F3Q004400010006AA000300380001000200044F3Q003800012Q009901036Q006D01043Q00020010E1000400040002001269010500014Q00030005000100020010E10004000200052Q007B00033Q00042Q00E2000200024Q0064012Q00017Q00053Q0003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03043Q004E616D6501153Q00060D012Q00040001000100044F3Q000400012Q001A2Q0100014Q00E2000100023Q0012692Q0100013Q00201801023Q00022Q0041000200034Q00222Q013Q000300044F3Q00100001002018010600050003001243000800044Q00440006000800020006080106001000013Q00044F3Q0010000100204D0106000500052Q00E2000600023Q0006AA000100090001000200044F3Q000900012Q001A2Q0100014Q00E2000100024Q0064012Q00017Q00103Q0003043Q007469636B03043Q0074696D65027Q004003043Q006F72657303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C030E3Q0047657444657363656E64616E747303043Q004E616D652Q033Q004F7265030C3Q00476574412Q74726962757465034Q0003053Q007461626C6503043Q0066696E6403063Q00696E73657274014C3Q00060D012Q00040001000100044F3Q000400012Q006D2Q016Q00E2000100024Q00992Q016Q00C0000100013Q001269010200014Q00030002000100020006082Q01001000013Q00044F3Q0010000100204D0103000100022Q0079010300020003002624010300100001000300044F3Q0010000100204D0103000100042Q00E2000300024Q006D01036Q001A010400043Q0012F0000500053Q00202Q00063Q00064Q000600076Q00053Q000700044Q001E0001002018010A00090007001243000C00084Q0044000A000C0002000608010A001E00013Q00044F3Q001E00012Q0090010400093Q00044F3Q002000010006AA000500170001000200044F3Q0017000100060D010400230001000100044F3Q002300012Q009001045Q001269010500053Q0020180106000400092Q0041000600074Q002201053Q000700044F3Q0043000100204D010A0009000A0026DF000A00430001000B00044F3Q00430001002018010A00090007001243000C00084Q0044000A000C0002000608010A004300013Q00044F3Q00430001002018010A0009000C001243000C000B4Q0044000A000C0002000608010A004300013Q00044F3Q004300010026E5000A00430001000D00044F3Q00430001001269010B000E3Q002079000B000B000F4Q000C00036Q000D000A6Q000B000D000200062Q000B00430001000100044F3Q00430001001269010B000E3Q00204D010B000B00102Q0090010C00034Q0090010D000A4Q0026010B000D00010006AA000500280001000200044F3Q002800012Q009901056Q006D01063Q00020010E10006000400030010E10006000200022Q007B00053Q00062Q00E2000300024Q0064012Q00017Q000B3Q00030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C028Q0003053Q007461626C6503043Q0066696E64026Q00F03F01394Q009100018Q00025Q00202Q00020002000100122Q000400026Q00020004000200062Q000200080001000100044F3Q000800012Q00E2000100023Q001269010300033Q0020180104000200042Q0041000400054Q002201033Q000500044F3Q00350001002018010800070005001243000A00064Q00440008000A000200060D010800170001000100044F3Q00170001002018010800070005001243000A00074Q00440008000A00020006080108003500013Q00044F3Q00350001001269010800033Q0020180109000700042Q00410009000A4Q002201083Q000A00044F3Q003300012Q0099010D00014Q0090010E000C4Q0031000D00020002000608010D003300013Q00044F3Q00330001000608012Q002D00013Q00044F3Q002D00012Q0034000E5Q0026E5000E002D0001000800044F3Q002D0001001269010E00093Q002084010E000E000A4Q000F8Q0010000D6Q000E0010000200062Q000E003300013Q00044F3Q003300012Q00C0000E0001000D00060D010E00310001000100044F3Q00310001001243000E00083Q00207D000E000E000B2Q007B0001000D000E0006AA0008001C0001000200044F3Q001C00010006AA0003000D0001000200044F3Q000D00012Q00E2000100024Q0064012Q00017Q000D3Q00028Q0003203Q00F09F938A202873656C65637420726F636B7320746F20732Q6520636F756E742903063Q0069706169727303053Q007461626C6503063Q00696E7365727403023Q003A20026Q00F03F030C3Q00F09F938A20466F756E643A20030C3Q00F09F938A20546F74616C3A2003023Q00202803063Q00636F6E63617403023Q002C2003013Q002901333Q000608012Q000500013Q00044F3Q000500012Q003400015Q0026DF000100070001000100044F3Q00070001001243000100024Q00E2000100024Q00992Q016Q003700028Q0001000200024Q00025Q00122Q000300013Q00122Q000400036Q00058Q00040002000600044Q001D00012Q00C000090001000800060D010900140001000100044F3Q00140001001243000900014Q006200030003000900126A010A00043Q00202Q000A000A00054Q000B00026Q000C00083Q00122Q000D00066Q000E00096Q000C000C000E4Q000A000C00010006AA000400100001000200044F3Q001000012Q003400045Q0026DF000400270001000700044F3Q00270001001243000400084Q0090010500034Q00ED0004000400052Q00E2000400023Q00044F3Q00320001001243000400094Q0064000500033Q00122Q0006000A3Q00122Q000700043Q00202Q00070007000B4Q000800023Q00122Q0009000C6Q00070009000200122Q0008000D6Q0004000400084Q000400024Q0064012Q00017Q00013Q0003053Q007063612Q6C000A4Q0099016Q000608012Q000900013Q00044F3Q00090001001269012Q00013Q0006822Q013Q000100012Q0099017Q007B012Q000200012Q001A017Q0097017Q0064012Q00013Q00013Q00023Q0003043Q007461736B03063Q0063616E63656C00053Q001269012Q00013Q00204D014Q00022Q00992Q016Q007B012Q000200012Q0064012Q00017Q00023Q0003043Q007461736B03053Q00737061776E000B4Q0099017Q00A43Q00010001001269012Q00013Q00204D014Q00020006822Q013Q000100032Q0099012Q00024Q0099012Q00034Q0099012Q00044Q00313Q000200022Q0097012Q00014Q0064012Q00013Q00013Q00083Q00030A3Q004175746F4D696E696E6703043Q007461736B03043Q0077616974026Q000840030E3Q00526F636B436F756E744C6162656C030D3Q0053656C6563746564526F636B73028Q0003053Q007063612Q6C001E4Q0099016Q00204D014Q0001000608012Q001D00013Q00044F3Q001D0001001269012Q00023Q0020085Q000300122Q000100048Q000200019Q0000206Q000100064Q000D0001000100044F3Q000D000100044F3Q001D00012Q0099012Q00013Q00204D014Q0005000608014Q00013Q00044F5Q00012Q0099016Q00204D014Q00062Q00347Q000ED500073Q00013Q00044F5Q0001001269012Q00083Q0006822Q013Q000100032Q0099012Q00014Q0099012Q00024Q0099017Q007B012Q0002000100044F5Q00012Q0064012Q00013Q00013Q00033Q00030E3Q00526F636B436F756E744C6162656C2Q033Q00536574030D3Q0053656C6563746564526F636B7300094Q009F7Q00206Q000100206Q00024Q000200016Q000300023Q00202Q0003000300034Q000200039Q0000016Q00017Q000B3Q00030B3Q005A6F6E65456E61626C6564030A3Q005A6F6E6543656E74657203013Q005803083Q005A6F6E654C65667403093Q005A6F6E65526967687403013Q005903083Q005A6F6E65446F776E03063Q005A6F6E65557003013Q005A03093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B01364Q00992Q015Q00204D2Q010001000100060D2Q0100060001000100044F3Q000600012Q008B2Q0100014Q00E2000100024Q00992Q015Q00204D2Q010001000200204D01023Q000300206C0003000100034Q00045Q00202Q0004000400044Q00030003000400062Q000300320001000200044F3Q0032000100204D01023Q000300204D0103000100032Q009901045Q00204D0104000400052Q00620003000300040006F4000200320001000300044F3Q0032000100204D01023Q000600206C0003000100064Q00045Q00202Q0004000400074Q00030003000400062Q000300320001000200044F3Q0032000100204D01023Q000600204D0103000100062Q009901045Q00204D0104000400082Q00620003000300040006F4000200320001000300044F3Q0032000100204D01023Q000900206C0003000100094Q00045Q00202Q00040004000A4Q00030003000400062Q000300320001000200044F3Q0032000100204D01023Q000900204D0103000100092Q009901045Q00204D01040004000B2Q006200030003000400065C010200020001000300044F3Q003300012Q00EF00026Q008B010200014Q00E2000200024Q0064012Q00017Q00093Q00026Q005940030C3Q00536B692Q706564526F636B730003103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B7303043Q007479706503063Q006E756D62657203043Q007469636B013F4Q00992Q016Q009001026Q00310001000200020006082Q01001500013Q00044F3Q00150001000E80000100150001000100044F3Q001500012Q0099010200013Q0020A501020002000200202Q00023Q00034Q000200013Q00202Q00020002000400202Q00023Q00034Q000200013Q00202Q00020002000500202Q00023Q00034Q000200013Q00202Q00020002000600202Q00023Q00034Q00028Q000200024Q0099010200013Q00204D0102000200042Q00C0000200023Q0006080102001C00013Q00044F3Q001C00012Q008B010200014Q00E2000200024Q0099010200013Q00204D0102000200022Q00C0000200023Q00060D010200230001000100044F3Q002300012Q008B01026Q00E2000200024Q0099010200013Q0020870002000200024Q000200023Q00122Q000300076Q000400026Q00030002000200262Q0003003C0001000800044F3Q003C0001001269010300094Q00030003000100020006F40002003A0001000300044F3Q003A00012Q0099010300013Q00204D01030003000200201200033Q00032Q0099010300013Q00204D01030003000500201200033Q00032Q0099010300013Q00204D01030003000600201200033Q00032Q008B01036Q00E2000300024Q008B010300014Q00E2000300024Q008B01036Q00E2000300024Q0064012Q00017Q000D3Q0003043Q007469636B028Q0003053Q007061697273030C3Q00536B692Q706564526F636B7303063Q00506172656E74026Q00594000030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B73026Q00F03F03043Q007479706503063Q006E756D62657203103Q004F726546696C7465726564526F636B7300513Q001265012Q00018Q0001000200122Q000100023Q00122Q000200036Q00035Q00202Q0003000300044Q00020002000400044Q003000012Q0099010700014Q0090010800054Q00310007000200020006080105001400013Q00044F3Q0014000100204D0108000500050006080108001400013Q00044F3Q001400010006080107001F00013Q00044F3Q001F0001000E800006001F0001000700044F3Q001F00012Q009901085Q00207401080008000400202Q0008000500074Q00085Q00202Q00080008000800202Q0008000500074Q00085Q00202Q00080008000900202Q00080005000700202Q00010001000A00044F3Q003000010012690108000B4Q0090010900064Q00310008000200020026DF000800300001000C00044F3Q003000010006F40006003000013Q00044F3Q003000012Q009901085Q00207401080008000400202Q0008000500074Q00085Q00202Q00080008000800202Q0008000500074Q00085Q00202Q00080008000900202Q00080005000700202Q00010001000A0006AA000200080001000200044F3Q00080001001269010200034Q009901035Q00204D01030003000D2Q001C00020002000400044F3Q004D00012Q0099010600014Q0090010700054Q00310006000200020006080105004300013Q00044F3Q0043000100204D0107000500050006080107004300013Q00044F3Q004300010006080106004D00013Q00044F3Q004D0001000E800006004D0001000600044F3Q004D00012Q009901075Q00207401070007000D00202Q0007000500074Q00075Q00202Q00070007000800202Q0007000500074Q00075Q00202Q00070007000900202Q00070005000700202Q00010001000A0006AA000200370001000100044F3Q003700012Q00E2000100024Q0064012Q00017Q000B3Q0003043Q007469636B028Q0003053Q007061697273030F3Q004F7265536B69704E6F74696669656403063Q00506172656E7400026Q00F03F030D3Q004F7265436865636B4C6576656C03043Q007479706503063Q006E756D626572025Q00C0724000303Q001265012Q00018Q0001000200122Q000100023Q00122Q000200036Q00035Q00202Q0003000300044Q00020002000400044Q002C00010006080105000D00013Q00044F3Q000D000100204D01070005000500060D010700120001000100044F3Q001200012Q009901075Q00204D01070007000400201200070005000600207D00010001000700044F3Q002C00012Q0099010700014Q0090010800054Q00310007000200020006080107002000013Q00044F3Q002000012Q0099010800023Q00204D01080008000800067A000800200001000700044F3Q002000012Q009901085Q00204D01080008000400201200080005000600207D00010001000700044F3Q002C0001001269010800094Q0090010900064Q00310008000200020026DF0008002C0001000A00044F3Q002C00012Q007901083Q0006000ED5000B002C0001000800044F3Q002C00012Q009901085Q00204D01080008000400201200080005000600207D0001000100070006AA000200080001000200044F3Q000800012Q00E2000100024Q0064012Q00017Q00123Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7303063Q006970616972732Q01030D3Q0053656C6563746564526F636B7303053Q007461626C6503063Q00696E73657274030E3Q00526F636B5072696F726974696573026Q00F03F030C3Q00526F636B44726F70646F776E03053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403113Q00526F636B73207265667265736865643A2003083Q004475726174696F6E027Q0040030F3Q004C617374526F636B5265667265736803043Q007469636B01574Q003Q018Q000200016Q0001000200014Q000100013Q00202Q00010001000100062Q0001003900013Q00044F3Q003900012Q006D2Q015Q001269010200024Q0099010300024Q001C00020002000400044F3Q000D00010020120001000600030006AA0002000C0001000200044F3Q000C00012Q006D01025Q001239010300026Q000400013Q00202Q0004000400044Q00030002000500044Q001D00012Q00C00008000100070006080108001D00013Q00044F3Q001D0001001269010800053Q00204D0108000800062Q0090010900024Q0090010A00074Q00260108000A00010006AA000300150001000200044F3Q001500012Q0034000300024Q0099010400013Q00204D0104000400042Q0034000400043Q0006A7000300390001000400044F3Q003900012Q0099010300013Q0010550103000400024Q000300016Q00045Q00102Q00030007000400122Q000300026Q000400013Q00202Q0004000400044Q00030002000500044Q003700012Q0099010800013Q0020010008000800074Q000900013Q00202Q0009000900044Q000900096Q00090009000600202Q0009000900084Q0008000700090006AA0003002F0001000200044F3Q002F00012Q00992Q0100033Q0006082Q01004600013Q00044F3Q004600012Q00992Q0100033Q00204D2Q01000100090006082Q01004600013Q00044F3Q004600010012692Q01000A3Q00068201023Q000100032Q0099012Q00034Q0099012Q00024Q0099012Q00014Q007B2Q010002000100060D012Q00520001000100044F3Q005200012Q00992Q0100044Q001B01023Q000300302Q0002000B000C00122Q0003000E6Q000400026Q000400046Q00030003000400102Q0002000D000300302Q0002000F00104Q0001000200012Q00992Q0100053Q001269010200124Q00030002000100020010E10001001100022Q0064012Q00013Q00013Q00063Q00030C3Q00526F636B44726F70646F776E03073Q0052656672657368028Q0003123Q00284E6F20726F636B7320696E206172656129030D3Q0053656C6563746564526F636B732Q033Q00536574001A4Q00C67Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200044F3Q000A00012Q0099010200013Q00060D0102000D0001000100044F3Q000D00012Q006D010200013Q001243000300044Q00050002000100012Q0026012Q000200012Q0099012Q00023Q00204D014Q00052Q00347Q000ED50003001900013Q00044F3Q001900012Q0099016Q0020395Q000100206Q00064Q000200023Q00202Q0002000200056Q000200012Q0064012Q00017Q00083Q0003043Q007469636B03083Q00746F6E756D62657203133Q00526F636B52656672657368496E74657276616C028Q0003183Q00526F636B526566726573684E6F54617267657444656C6179030F3Q004C617374526F636B52656672657368030D3Q004E6F54617267657453696E63650001313Q0006332Q01000400013Q00044F3Q000400010012692Q0100014Q0003000100010002001269010200024Q009901035Q00204D0103000300032Q003100020002000200060D0102000B0001000100044F3Q000B0001001243000200043Q001269010300024Q009901045Q00204D0104000400052Q003100030002000200060D010300120001000100044F3Q00120001001243000300043Q000ED5000400200001000200044F3Q002000012Q0099010400013Q00204D01040004000600060D010400190001000100044F3Q00190001001243000400044Q00790104000100040006F4000200200001000400044F3Q002000012Q0099010400024Q008B010500014Q007B0104000200012Q0064012Q00014Q0099010400013Q00204D0104000400070006080104003000013Q00044F3Q00300001000ED5000400300001000300044F3Q003000012Q0099010400013Q00204D0104000400072Q00790104000100040006F4000300300001000400044F3Q003000012Q0099010400024Q008B010500014Q007B0104000200012Q0099010400013Q00306D0004000700082Q0064012Q00017Q00033Q0003153Q005072696F7269747954797065432Q6F6C646F776E7303043Q007469636B00011B3Q000608012Q000600013Q00044F3Q000600012Q00992Q015Q00204D2Q010001000100060D2Q0100080001000100044F3Q000800012Q008B2Q016Q00E2000100024Q00992Q015Q00204D2Q01000100012Q00C0000100013Q00060D2Q01000F0001000100044F3Q000F00012Q008B01026Q00E2000200023Q001269010200024Q00030002000100020006F4000100180001000200044F3Q001800012Q009901025Q00204D01020002000100201200023Q00032Q008B01026Q00E2000200024Q008B010200014Q00E2000200024Q0064012Q00017Q00033Q00028Q0003153Q005072696F7269747954797065432Q6F6C646F776E7303043Q007469636B02153Q000608012Q000600013Q00044F3Q000600010006082Q01000600013Q00044F3Q000600010026E7000100070001000100044F3Q000700012Q0064012Q00014Q009901025Q00204D01020002000200060D0102000E0001000100044F3Q000E00012Q009901026Q006D01035Q0010E10002000200032Q009901025Q00204D010200020002001269010300034Q00030003000100022Q00620003000300012Q007B00023Q00032Q0064012Q00017Q00023Q00030C3Q004D617463686564526F636B730001063Q000608012Q000500013Q00044F3Q000500012Q00992Q015Q00204D2Q010001000100201200013Q00022Q0064012Q00017Q00023Q00030F3Q004F7265536B69704E6F7469666965640001093Q000608012Q000800013Q00044F3Q000800012Q00992Q015Q00205500010001000100202Q00013Q00024Q000100016Q00028Q0001000200012Q0064012Q00017Q00023Q00030F3Q004F7265536B69704E6F7469666965640001063Q000608012Q000500013Q00044F3Q000500012Q00992Q015Q00204D2Q010001000100201200013Q00022Q0064012Q00017Q00093Q00030E3Q00526F636B4F726546696C7465727303063Q0069706169727303043Q00526F636B03043Q004F726573028Q0003043Q00736C6F7403113Q00557365476C6F62616C46612Q6C6261636B030C3Q0053656C65637465644F72657303063Q00676C6F62616C01343Q00060D012Q00040001000100044F3Q000400012Q001A2Q0100024Q00AD000100034Q00992Q015Q00204D2Q01000100010006082Q01002000013Q00044F3Q002000010012692Q0100024Q009901025Q00204D0102000200012Q001C00010002000300044F3Q001E00010006080105001E00013Q00044F3Q001E000100204D0106000500030006180006001E00013Q00044F3Q001E000100204D0106000500040006080106001E00013Q00044F3Q001E000100204D0106000500042Q0034000600063Q000ED50005001E0001000600044F3Q001E000100204D010600050004001243000700064Q0090010800044Q00ED0007000700082Q00AD000600033Q0006AA0001000D0001000200044F3Q000D00012Q00992Q015Q00204D2Q01000100070006082Q01003100013Q00044F3Q003100012Q00992Q015Q00204D2Q01000100080006082Q01003100013Q00044F3Q003100012Q00992Q015Q00204D2Q01000100082Q0034000100013Q000ED5000500310001000100044F3Q003100012Q00992Q015Q00204D2Q0100010008001243000200094Q00AD000100034Q001A2Q0100024Q00AD000100034Q0064012Q00017Q00133Q0003113Q0041637469766546696C7465724C6162656C030B3Q0043752Q72656E74526F636B03053Q007063612Q6C028Q00030F3Q004163746976652046696C7465723A2003063Q00676C6F62616C03083Q00476C6F62616C202803083Q00746F737472696E6703063Q00206F7265732903083Q00746F6E756D62657203053Q006D61746368030B3Q005E736C6F742825642B292403053Q00536C6F742003023Q002028030E3Q00526F636B4F726546696C7465727303063Q0069706169727303043Q00526F636B03113Q00557365476C6F62616C46612Q6C6261636B030C3Q0053656C65637465644F72657301824Q00992Q015Q00204D2Q010001000100060D2Q0100050001000100044F3Q000500012Q0064012Q00013Q0006332Q01001200013Q00044F3Q001200012Q00992Q0100013Q00204D2Q01000100020006082Q01001100013Q00044F3Q001100012Q00992Q0100024Q0099010200013Q00204D0102000200022Q003100010002000200060D2Q0100120001000100044F3Q001200012Q001A2Q0100013Q00060D2Q0100190001000100044F3Q00190001001269010200033Q00068201033Q000100012Q0099017Q007B0102000200012Q0064012Q00014Q0099010200034Q0090010300014Q001C0002000200030006080102005000013Q00044F3Q005000012Q0034000400023Q000ED5000400500001000400044F3Q005000010006080103005000013Q00044F3Q00500001001243000400053Q0026DF0003002E0001000600044F3Q002E00012Q0090010500043Q00126C010600073Q00122Q000700086Q000800026Q00070002000200122Q000800096Q00040005000800044Q004900010012690105000A3Q0012C4000600086Q000700036Q00060002000200202Q00060006000B00122Q0008000C6Q000600086Q00053Q000200062Q0005004400013Q00044F3Q004400012Q0090010600043Q0012430007000D3Q001269010800084Q0090010900054Q003100080002000200126C0109000E3Q00122Q000A00086Q000B00026Q000A0002000200122Q000B00096Q00040006000B00044Q004900012Q0090010600043Q001269010700084Q0090010800034Q00310007000200022Q00ED000400060007001269010500033Q00068201060001000100022Q0099017Q0090012Q00044Q007B0105000200012Q0064012Q00014Q005800046Q001A010400044Q0099010500043Q00204D01050005000F0006080105006300013Q00044F3Q00630001001269010500104Q0099010600043Q00204D01060006000F2Q001C00050002000700044F3Q006100010006080109006100013Q00044F3Q0061000100204D010A00090011000618000A00610001000100044F3Q006100012Q0090010400083Q00044F3Q006300010006AA0005005A0001000200044F3Q005A00010006080104006B00013Q00044F3Q006B0001001269010500033Q00068201060002000100022Q0099017Q0090012Q00044Q007B01050002000100044F3Q008100012Q0099010500043Q00204D01050005001200060D0105007D0001000100044F3Q007D00012Q0099010500043Q00204D0105000500130006080105007D00013Q00044F3Q007D00012Q0099010500043Q00204D0105000500132Q0034000500053Q000ED50004007D0001000500044F3Q007D0001001269010500033Q00068201060003000100012Q0099017Q007B01050002000100044F3Q00810001001269010500033Q00068201060004000100012Q0099017Q007B0105000200012Q0064012Q00013Q00053Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403133Q004163746976652046696C7465723A204E6F6E6500064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00023Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657400064Q00787Q00206Q000100206Q00024Q000200018Q000200016Q00017Q00053Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403143Q004163746976652046696C7465723A20536C6F742003083Q00746F737472696E67030A3Q0020286E6F206F72657329000B4Q0099016Q00204D014Q0001002018014Q0002001243000200033Q001269010300044Q0099010400014Q0031000300020002001243000400054Q00ED0002000200042Q0026012Q000200012Q0064012Q00017Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403203Q004163746976652046696C7465723A204E6F6E652028676C6F62616C206F2Q662900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403133Q004163746976652046696C7465723A204E6F6E6500064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00053Q00030C3Q0043752Q72656E745068617365026Q001040030B3Q0043752Q72656E74526F636B03113Q004C6173744F7265536B69704E6F7469667903043Q007469636B021B3Q000633010200040001000100044F3Q000400012Q009901025Q00204D0102000200010026E5000200080001000200044F3Q000800012Q008B01036Q00E2000300023Q000608012Q001400013Q00044F3Q001400012Q009901035Q00204D0103000300030006080103001400013Q00044F3Q001400012Q009901035Q00204D0103000300030006A73Q00140001000300044F3Q001400012Q008B01036Q00E2000300024Q009901035Q00129C000400056Q00040001000200102Q0003000400044Q000300016Q000300028Q00017Q001B3Q00030D3Q004F7265536B69704E6F74696679030F3Q004F7265536B69704E6F74696669656403043Q007469636B03083Q00746F737472696E6703013Q002503013Q003F03043Q006D61746803053Q00666C2Q6F72028Q0003143Q004F726520536B69702028526F636B20547970652903063Q00737472696E6703063Q00666F726D617403143Q00E29D8C2025730AF09F8EAF2057616E743A20257303073Q00556E6B6E6F776E03063Q00286E6F6E652903133Q004F726520536B697020284D69736D617463682903143Q004F726520536B697020285072652D436865636B2903273Q00F09FAAA820257320402025730AF09F928E204861733A2025730AF09F8EAF2057616E743A20257303043Q006E6F6E6503103Q000AE28FB1EFB88F20536B69702025647303183Q000AE28FB1EFB88F20536B697020756E74696C20726567656E031C3Q0025732040202573207C204861733A202573207C2057616E743A20257303053Q005469746C6503083Q004F726520536B697003073Q00436F6E74656E7403083Q004475726174696F6E026Q001040087A4Q009901085Q00204D01080008000100060D010800050001000100044F3Q000500012Q0064012Q00014Q0099010800014Q0090010900064Q0090010A00074Q00440008000A000200060D0108000C0001000100044F3Q000C00012Q0064012Q00013Q0006080106001800013Q00044F3Q001800012Q0099010800023Q00204D0108000800022Q00C000080008000600060D010800180001000100044F3Q001800012Q0099010800023Q00204D010800080002001269010900034Q00030009000100022Q007B0008000600090006080102002100013Q00044F3Q00210001001269010800044Q002D010900026Q00080002000200122Q000900056Q00080008000900062Q000800220001000100044F3Q00220001001243000800063Q0006080105002A00013Q00044F3Q002A0001001269010900073Q00204D0109000900082Q0090010A00054Q003100090002000200060D0109002B0001000100044F3Q002B0001001243000900094Q001A010A000A3Q0026DF3Q003C0001000A00044F3Q003C0001001269010B000B3Q00204D010B000B000C001243000C000D3Q001269010D00043Q000633010E00350001000100044F3Q00350001001243000E000E4Q0031000D00020002000633010E00390001000400044F3Q00390001001243000E000F4Q0044000B000E00022Q0090010A000B3Q00044F3Q007000010026E53Q00400001001000044F3Q004000010026DF3Q005F0001001100044F3Q005F0001001269010B000B3Q00204D010B000B000C001243000C00123Q001269010D00043Q000633010E00470001000100044F3Q00470001001243000E000E4Q0031000D000200022Q0090010E00083Q000633010F004C0001000300044F3Q004C0001001243000F00133Q0006330110004F0001000400044F3Q004F00010012430010000F4Q0044000B001000022Q0090010A000B3Q000ED50009005B0001000900044F3Q005B00012Q0090010B000A3Q0012F8000C000B3Q00202Q000C000C000C00122Q000D00146Q000E00096Q000C000E00024Q000A000B000C00044Q007000012Q0090010B000A3Q001243000C00154Q00ED000A000B000C00044F3Q00700001001269010B000B3Q00204D010B000B000C001243000C00163Q001269010D00043Q000633010E00660001000100044F3Q00660001001243000E000E4Q0031000D000200022Q0090010E00083Q000633010F006B0001000300044F3Q006B0001001243000F00133Q0006330110006E0001000400044F3Q006E00010012430010000F4Q0044000B001000022Q0090010A000B4Q0099010B00034Q006D010C3Q0003000633010D007500013Q00044F3Q00750001001243000D00183Q0010E1000C0017000D0010E1000C0019000A00306D000C001A001B2Q007B010B000200012Q0064012Q00017Q00063Q0003063Q00697061697273034Q0003063Q00286E6F6E652903053Q007461626C6503063Q00696E736572743Q011C4Q006D2Q015Q00060D012Q00040001000100044F3Q000400012Q00E2000100024Q006D01025Q001269010300014Q009001046Q001C00030002000500044F3Q001800010006080107001800013Q00044F3Q001800010026E5000700180001000200044F3Q001800010026E5000700180001000300044F3Q001800012Q00C000080002000700060D010800180001000100044F3Q00180001001269010800043Q0020460108000800054Q000900016Q000A00076Q0008000A000100202Q0002000700060006AA000300090001000200044F3Q000900012Q00E2000100024Q0064012Q00017Q00083Q00026Q00F03F026Q000840030E3Q00526F636B4F726546696C7465727303043Q00526F636B0003043Q004F726573034Q0003143Q00284E6F20726F636B7320617661696C61626C6529032C3Q0026633Q00040001000100044F3Q00040001000ED50002000500013Q00044F3Q000500012Q0064012Q00014Q009901035Q00204D01030003000300060D010300190001000100044F3Q001900012Q009901036Q0007010400036Q00053Q000200302Q0005000400054Q00065Q00102Q0005000600064Q00063Q000200302Q0006000400054Q00075Q00102Q0006000600074Q00073Q000200302Q0007000400054Q00085Q00102Q0007000600084Q0004000300010010E10003000300042Q009901035Q00204D0103000300032Q006D01043Q00020006082Q01002400013Q00044F3Q002400010026E5000100240001000700044F3Q002400010026E5000100240001000800044F3Q00240001000633010500250001000100044F3Q002500012Q001A010500053Q0010E10004000400052Q009B010500016Q000600026Q00050002000200102Q0004000600054Q00033Q00046Q00017Q00053Q00026Q00F03F026Q000840030E3Q00526F636B4F726546696C7465727303043Q00526F636B03043Q004F726573011D3Q0026633Q00040001000100044F3Q00040001000ED50002000700013Q00044F3Q000700012Q001A2Q0100014Q006D01026Q00AD000100034Q00992Q015Q00204D2Q01000100030006082Q01001000013Q00044F3Q001000012Q00992Q015Q00204D2Q01000100032Q00C0000100013Q00060D2Q0100130001000100044F3Q001300012Q001A2Q0100014Q006D01026Q00AD000100034Q00992Q015Q0020422Q01000100034Q000100013Q00202Q00020001000400202Q00030001000500062Q0003001B0001000100044F3Q001B00012Q006D01036Q00AD000200034Q0064012Q00017Q00063Q0003063Q00506172656E74030D3Q0053656C6563746564526F636B73028Q0003053Q00706169727303043Q0066696E6403083Q00506F736974696F6E02373Q000608012Q000500013Q00044F3Q0005000100204D01023Q000100060D010200070001000100044F3Q000700012Q008B01026Q00E2000200024Q009901026Q009001036Q003100020002000200060D0102000E0001000100044F3Q000E00012Q008B01036Q00E2000300024Q0099010300013Q00204D0103000300022Q0034000300033Q000ED50003002D0001000300044F3Q002D00012Q0099010300024Q009001046Q00310003000200020006080103002D00013Q00044F3Q002D00012Q008B01045Q001239010500046Q000600013Q00202Q0006000600024Q00050002000700044Q002700010006A7000300250001000900044F3Q00250001002018010A000300052Q0090010C00094Q0044000A000C0002000608010A002700013Q00044F3Q002700012Q008B010400013Q00044F3Q002900010006AA0005001E0001000200044F3Q001E000100060D0104002D0001000100044F3Q002D00012Q008B01056Q00E2000500024Q0099010300033Q00204D0104000200062Q003100030002000200060D010300340001000100044F3Q003400012Q008B01036Q00E2000300024Q008B010300014Q00E2000300024Q0064012Q00017Q00103Q00030F3Q005072696F72697479456E61626C6564030D3Q0053656C6563746564526F636B73027Q0040030E3Q00526F636B5072696F726974696573028Q0003053Q00706169727303083Q00506F736974696F6E030D3Q0053656C65637465644172656173030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C030E3Q0046696E6446697273744368696C6403063Q00737472696E6703063Q00666F726D6174033C3Q00205072696F726974792025642025733A20466F756E643A256420536B69703A2564204E6F4869743A256420496E76616C69643A2564204661723A2564019F4Q00992Q015Q00204D2Q010001000100060D2Q0100060001000100044F3Q000600012Q001A2Q0100014Q00E2000100024Q00992Q015Q00204D2Q01000100022Q0034000100013Q0026242Q01000D0001000300044F3Q000D00012Q001A2Q0100014Q00E2000100024Q00992Q0100014Q009001026Q003100010002000200060D2Q0100140001000100044F3Q001400012Q001A010200024Q00E2000200024Q009901025Q00204D0102000200042Q00C000020002000100060D0102001A0001000100044F3Q001A0001001243000200053Q001243000300053Q001239010400066Q00055Q00202Q0005000500044Q00040002000600044Q0023000100067A000300230001000800044F3Q002300012Q0090010300083Q0006AA000400200001000200044F3Q002000010006F4000300290001000200044F3Q002900012Q001A010400044Q00E2000400024Q0099010400024Q009E0104000100024Q000500036Q000600046Q00050002000200062Q000500320001000100044F3Q003200012Q001A010600064Q00E2000600023Q00204D0106000500072Q0099010700044Q000300070001000200060D010700390001000100044F3Q003900012Q001A010800084Q00E2000800023Q001269010800064Q009901095Q00204D0109000900042Q001C00080002000A00044F3Q009A000100067A000200990001000C00044F3Q009900012Q0099010D00054Q0090010E000B4Q0031000D0002000200060D010D00990001000100044F3Q00990001001243000D00053Q001243000E00053Q001243000F00053Q001243001000053Q001243001100053Q00068201123Q0001000F2Q0099012Q00014Q0090012Q000B4Q0090012Q000D4Q0099012Q00064Q0090012Q000E4Q0099012Q00074Q0099012Q00084Q0090012Q000F4Q0099012Q00094Q0090012Q00104Q0090012Q00064Q0099017Q0090012Q00114Q0099012Q000A4Q0090012Q000C4Q009901135Q00204D0113001300082Q0034001300133Q0026DF001300770001000500044F3Q00770001001269011300063Q0020180114000700092Q0041001400154Q002201133Q001500044F3Q0074000100201801180017000A001243001A000B4Q00440018001A000200060D0118006E0001000100044F3Q006E000100201801180017000A001243001A000C4Q00440018001A00020006080118007400013Q00044F3Q007400012Q0090011800124Q0090011900174Q00310018000200020006080118007400013Q00044F3Q007400012Q00E2001800023Q0006AA001300640001000200044F3Q0064000100044F3Q00890001001269011300064Q009901145Q00204D0114001400082Q001C00130002001500044F3Q0087000100201801180007000D2Q0090011A00174Q00440018001A00020006080118008700013Q00044F3Q008700012Q0090011900124Q0090011A00184Q00310019000200020006080119008700013Q00044F3Q008700012Q00E2001900023Q0006AA0013007C0001000200044F3Q007C0001000ED5000500980001000D00044F3Q009800012Q00990113000A3Q0012690114000E3Q00204D01140014000F001243001500104Q00900116000C4Q00900117000B4Q00900118000D4Q00900119000E4Q0090011A000F4Q0090011B00104Q0090011C00114Q00CB0014001C4Q00B600133Q00012Q0058000D6Q0058000B5Q0006AA0008003E0001000200044F3Q003E00012Q001A010800084Q00E2000800024Q0064012Q00013Q00013Q000A3Q0003053Q007061697273030B3Q004765744368696C6472656E026Q00F03F030C3Q00536B692Q706564526F636B7303083Q00506F736974696F6E03093Q004D61676E6974756465030B3Q004D696E696E6752616E676503063Q00737472696E6703063Q00666F726D6174032B3Q0020466F756E6420686967686572205020726F636B3A202573285025642920617420252E316620737475647301493Q0012F0000100013Q00202Q00023Q00024Q000200036Q00013Q000300044Q004400012Q009901066Q0090010700054Q00310006000200022Q0099010700013Q000618000600440001000700044F3Q004400012Q0099010700023Q0020470007000700034Q000700026Q000700036Q000800056Q00070002000200062Q0007001600013Q00044F3Q001600012Q0099010700043Q00207D0007000700032Q0097010700044Q0099010700053Q00204D0107000700042Q00C000070007000500060D010700440001000100044F3Q004400012Q0099010700064Q0090010800054Q003100070002000200060D010700240001000100044F3Q002400012Q0099010800073Q00207D0008000800032Q0097010800073Q00044F3Q004400012Q0099010800084Q0090010900054Q008B010A00014Q00440008000A000200060D0108002E0001000100044F3Q002E00012Q0099010800093Q00207D0008000800032Q0097010800093Q00044F3Q004400012Q00990108000A3Q0020880109000700054Q00080008000900202Q0008000800064Q0009000B3Q00202Q00090009000700062Q0009003A0001000800044F3Q003A00012Q00990109000C3Q00207D0009000900032Q00970109000C3Q00044F3Q004400012Q00990109000D3Q001275010A00083Q00202Q000A000A000900122Q000B000A6Q000C00016Q000D000E6Q000E00086Q000A000E6Q00093Q00014Q000500023Q0006AA000100050001000200044F3Q000500012Q001A2Q0100014Q00E2000100024Q0064012Q00017Q002C3Q0003083Q00506F736974696F6E03053Q00746F74616C028Q0003083Q006E6F486974626F7803083Q006E6F7456616C696403063Q00742Q6F46617203053Q00666F756E6403073Q00736B692Q706564030D3Q0053656C6563746564417265617303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C030E3Q0046696E6446697273744368696C64030E3Q00526F636B5072696F72697469657303113Q005072696F726974794C6F636B556E74696C03043Q007469636B03143Q004C6173745072696F72697479526F636B5479706503043Q006D61746803043Q006875676503063Q0069706169727303043Q006469737403053Q00737061776E03063Q00506172656E7403043Q004E616D6503073Q00556E6B6E6F776E03063Q00737472696E6703063Q00666F726D617403253Q00205072696F72697479204C4F434B3A20257320696E2025732028252E316620737475647329030F3Q005072696F72697479456E61626C6564030D3Q0053656C6563746564526F636B7303053Q007461626C6503063Q00696E7365727403083Q007072696F7269747903083Q00726F636B5479706503043Q00736F7274032C3Q00205072696F7269747920526F636B3A2025732028503A25642920696E2025732028252E316620737475647329032A3Q00205072696F726974792025643A202573206E6F7420666F756E642C20747279696E67206E6578743Q2E033C3Q00204E6F207072696F7269747920726F636B7320617661696C61626C652C2066612Q6C696E67206261636B20746F20616E792076616C696420726F636B03223Q0020526F636B20466F756E643A20257320696E2025732028252E31662073747564732903363Q00205343414E205354415453207C20546F74616C3A25642056616C69643A256420536B692Q7065643A25642046696C74657265643A2564034D3Q00204445425547207C20546F74616C3A2564204E6F486974626F783A2564204E6F7456616C69643A256420542Q6F4661723A256420536B692Q7065643A2564207C20506C61796572593A252E316603013Q00590048013Q00119Q003Q000100024Q000100016Q00028Q00010002000200062Q000100090001000100044F3Q000900012Q001A010200024Q00E2000200024Q0099010200024Q000300020001000200060D0102000F0001000100044F3Q000F00012Q001A010300034Q00E2000300023Q00204D0103000100012Q006D01043Q000600306D00040002000300306D00040004000300306D00040005000300306D00040006000300306D00040007000300306D0004000800032Q006D01055Q00068201063Q000100092Q0090012Q00044Q0099012Q00034Q0099012Q00044Q0099012Q00054Q0099012Q00064Q0090012Q00034Q0099012Q00074Q0099012Q00084Q0090012Q00054Q0099010700073Q00204D0107000700092Q0034000700073Q0026DF0007003C0001000300044F3Q003C00010012690107000A3Q00201801080002000B2Q0041000800094Q002201073Q000900044F3Q00390001002018010C000B000C001243000E000D4Q0044000C000E000200060D010C00360001000100044F3Q00360001002018010C000B000C001243000E000E4Q0044000C000E0002000608010C003900013Q00044F3Q003900012Q0090010C00064Q0090010D000B4Q007B010C000200010006AA0007002C0001000200044F3Q002C000100044F3Q004B00010012690107000A4Q0099010800073Q00204D0108000800092Q001C00070002000900044F3Q00490001002018010C0002000F2Q0090010E000B4Q0044000C000E0002000608010C004900013Q00044F3Q004900012Q0090010D00064Q0090010E000C4Q007B010D000200010006AA000700410001000200044F3Q004100012Q008B01075Q0012390108000A6Q000900073Q00202Q0009000900104Q00080002000A00044Q005300012Q008B010700013Q00044F3Q005500010006AA000800510001000100044F3Q005100012Q0099010800043Q00204D0108000800110006080108008D00013Q00044F3Q008D00012Q0099010800043Q00204D010800080011001269010900124Q000300090001000200067A0009008D0001000800044F3Q008D00012Q0099010800043Q00204D0108000800130006080108008D00013Q00044F3Q008D00012Q0099010800043Q00204D0108000800132Q00C00009000500080006080109008D00013Q00044F3Q008D00012Q0034000A00093Q000ED50003008D0001000A00044F3Q008D00012Q001A010A000A3Q001235010B00143Q00202Q000B000B001500122Q000C00166Q000D00096Q000C0002000E00044Q0077000100204D01110010001700067A001100770001000B00044F3Q0077000100204D010B0010001700204D010A001000180006AA000C00720001000200044F3Q00720001000608010A008D00013Q00044F3Q008D000100204D010C000A0019000608010C008200013Q00044F3Q0082000100204D010C000A001900204D010C000C001A00060D010C00830001000100044F3Q00830001001243000C001B4Q0099010D00093Q001217010E001C3Q00202Q000E000E001D00122Q000F001E6Q001000086Q0011000C6Q0012000B6Q000E00126Q000D3Q00014Q000A00024Q0099010800073Q00204D01080008001F000608010800F400013Q00044F3Q00F40001000608010700F400013Q00044F3Q00F400012Q0099010800073Q00204D0108000800202Q0034000800083Q000ED5000300F40001000800044F3Q00F400012Q006D01085Q001239010900166Q000A00073Q00202Q000A000A00204Q00090002000B00044Q00AB00012Q0099010E00073Q00204D010E000E00102Q00C0000E000E000D00060D010E00A40001000100044F3Q00A40001001243000E00033Q001269010F00213Q00204D010F000F00222Q0090011000084Q006D01113Q00020010E100110023000E0010E100110024000D2Q0026010F001100010006AA0009009E0001000200044F3Q009E0001001269010900213Q00204D0109000900252Q0090010A00083Q0002B3000B00014Q00A90009000B000100122Q000900166Q000A00086Q00090002000B00044Q00EF000100204D010E000D00242Q000A010F0005000E4Q0010000A6Q0011000E6Q00100002000200062Q001000BE00013Q00044F3Q00BE00012Q001A010F000F3Q000608010F00E700013Q00044F3Q00E700012Q00340010000F3Q000ED5000300E70001001000044F3Q00E700012Q001A011000103Q001235011100143Q00202Q00110011001500122Q001200166Q0013000F6Q00120002001400044Q00CF000100204D01170016001700067A001700CF0001001100044F3Q00CF000100204D01110016001700204D0110001600180006AA001200CA0001000200044F3Q00CA0001000608011000EF00013Q00044F3Q00EF000100204D011200100019000608011200DA00013Q00044F3Q00DA000100204D01120010001900204D01120012001A00060D011200DB0001000100044F3Q00DB00010012430012001B4Q0099011300093Q0012690114001C3Q00204D01140014001D001243001500264Q00900116000E3Q00204D0117000D00232Q0090011800124Q0090011900114Q00CB001400194Q00B600133Q00012Q00E2001000023Q00044F3Q00EF00012Q0099011000093Q00128F0111001C3Q00202Q00110011001D00122Q001200273Q00202Q0013000D00234Q0014000E6Q001100146Q00103Q00010006AA000900B60001000200044F3Q00B600012Q0099010900093Q001243000A00284Q007B0109000200012Q001A010800083Q001235010900143Q00202Q00090009001500122Q000A000A6Q000B00056Q000A0002000C00044Q000C2Q012Q0099010F000A4Q00900110000D4Q0031000F00020002000608010F003Q013Q00044F3Q003Q012Q001A010E000E3Q001269010F00164Q00900110000E4Q001C000F0002001100044F3Q000A2Q0100204D01140013001700067A0014000A2Q01000900044F3Q000A2Q0100204D01090013001700204D0108001300180006AA000F00052Q01000200044F3Q00052Q010006AA000A00FB0001000200044F3Q00FB0001000608010800372Q013Q00044F3Q00372Q0100204D010A00080019000608010A00172Q013Q00044F3Q00172Q0100204D010A0008001900204D010A000A001A00060D010A00182Q01000100044F3Q00182Q01001243000A001B4Q0099010B00093Q001269010C001C3Q00204D010C000C001D0012C1000D00296Q000E00086Q000F00086Q000E0002000200062Q000E00222Q01000100044F3Q00222Q01001243000E001B4Q0090010F000A4Q0072001000096Q000C00106Q000B3Q000100202Q000B00040008000E2Q0003002C2Q01000B00044F3Q002C2Q0100204D010B00040005000ED5000300462Q01000B00044F3Q00462Q012Q0099010B00093Q0012E6000C001C3Q00202Q000C000C001D00122Q000D002A3Q00202Q000E0004000200202Q000F0004000700202Q00100004000800202Q0011000400054Q000C00116Q000B3Q000100044Q00462Q0100204D010A00040002000ED5000300462Q01000A00044F3Q00462Q012Q0099010A00093Q001265000B001C3Q00202Q000B000B001D00122Q000C002B3Q00202Q000D0004000200202Q000E0004000400202Q000F0004000500202Q00100004000600202Q00110004000800202Q00120003002C4Q000B00124Q00B6000A3Q00012Q00E2000800024Q0064012Q00013Q00023Q00113Q0003053Q007061697273030B3Q004765744368696C6472656E03053Q00746F74616C026Q00F03F03073Q00736B692Q706564030C3Q00536B692Q706564526F636B7303083Q006E6F486974626F7803083Q006E6F7456616C696403083Q00506F736974696F6E03093Q004D61676E6974756465030B3Q004D696E696E6752616E676503063Q00742Q6F46617203053Q007461626C6503063Q00696E7365727403053Q00737061776E03043Q006469737403053Q00666F756E64015A3Q0012F0000100013Q00202Q00023Q00024Q000200036Q00013Q000300044Q005700012Q009901066Q009901075Q00204D01070007000300207D0007000700040010E10006000300072Q0099010600014Q0090010700054Q00310006000200020006080106001400013Q00044F3Q001400012Q009901066Q009901075Q00204D01070007000500207D0007000700040010E10006000500072Q0099010600023Q00204D0106000600062Q00C000060006000500060D010600570001000100044F3Q005700012Q0099010600034Q0090010700054Q003100060002000200060D010600240001000100044F3Q002400012Q009901076Q00A701085Q00202Q00080008000700202Q00080008000400102Q00070007000800044Q005700012Q0099010700044Q0090010800054Q008B010900014Q004400070009000200060D010700300001000100044F3Q003000012Q009901076Q00A701085Q00202Q00080008000800202Q00080008000400102Q00070008000800044Q005700012Q0099010700053Q0020880108000600094Q00070007000800202Q00070007000A4Q000800063Q00202Q00080008000B00062Q0008003E0001000700044F3Q003E00012Q009901086Q00A701095Q00202Q00090009000C00202Q00090009000400102Q0008000C000900044Q005700012Q0099010800074Q0090010900054Q00310008000200020006080108005700013Q00044F3Q005700012Q0099010900084Q00C000090009000800060D0109004A0001000100044F3Q004A00012Q0099010900084Q006D010A6Q007B00090008000A0012690109000D3Q0020E300090009000E4Q000A00086Q000A000A00084Q000B3Q000200102Q000B000F000500102Q000B001000074Q0009000B00014Q00098Q000A5Q00202Q000A000A001100202Q000A000A000400102Q00090011000A0006AA000100050001000200044F3Q000500012Q0064012Q00017Q00013Q0003083Q007072696F7269747902083Q00204D01023Q000100204D010300010001000600010300050001000200044F3Q000500012Q00EF00026Q008B010200014Q00E2000200024Q0064012Q00017Q00233Q00030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D6503043Q007469636B030B3Q0043752Q72656E74526F636B026Q00F03F030C3Q0043752Q72656E745068617365028Q00030D3Q004C6F636B65644D696E65506F730003063Q00737472696E6703063Q00666F726D617403213Q0020535455434B204C313A20506861736520726573657420286D696E65733A25642903123Q004D696E657353696E636548504368616E6765027Q004003083Q00506F736974696F6E03093Q004D61676E6974756465029A5Q99B93F03043Q00556E6974030E3Q00537475636B446574656374696F6E030E3Q00476C6974636844697374616E636503063Q00434672616D652Q033Q006E6577032D3Q0020535455434B204C323A20476C69746368202B256420737475647320286D696E65733A25642C204C3223256429030E3Q004C32412Q74656D7074436F756E74033E3Q0020535455434B204C323A204F2Q6673657420742Q6F20736D612Q6C2C20736B692Q70696E6720676C69746368206D6F766520746F2061766F6964204E614E026Q00084003333Q0020535455434B204C324C333A20457363616C6174696E672061667465722033206661696C6564204C3220612Q74656D70747321030A3Q00466C696768744D6F646503053Q0042656C6F7703063Q0048656967687403073Q00566563746F7233026Q00104003243Q0020535455434B204C333A20466F7263652074656C65706F727420286D696E65733A25642903043Q006D61746803053Q00666C2Q6F72018E4Q00FA00015Q00102Q000100016Q00015Q00122Q000200036Q00020001000200102Q0001000200024Q000100016Q0001000100024Q000200026Q000300016Q0002000200024Q00035Q00202Q00030003000400062Q000400120001000300044F3Q001200012Q0099010400034Q0090010500034Q003100040002000200060D010200150001000100044F3Q001500012Q0064012Q00013Q0026DF3Q00240001000500044F3Q002400012Q009901055Q00309B0005000600074Q00055Q00302Q0005000800094Q000500043Q00122Q0006000A3Q00202Q00060006000B00122Q0007000C6Q00085Q00202Q00080008000D4Q000600086Q00053Q000100044Q008500010026DF3Q005D0001000E00044F3Q005D00010006080104005D00013Q00044F3Q005D000100204D01050004000F00204D01060002000F2Q007901050005000600204D010600050010000ED5001100480001000600044F3Q0048000100204D0107000500120020D300080002000F4Q000900053Q00202Q00090009001300202Q0009000900144Q0009000700094Q00080008000900122Q000900153Q00202Q0009000900164Q000A00086Q00090002000200102Q0002001500094Q000900043Q00122Q000A000A3Q00202Q000A000A000B00122Q000B00176Q000C00053Q00202Q000C000C001300202Q000C000C00144Q000D5Q00202Q000D000D000D4Q000E5Q00202Q000E000E00184Q000A000E6Q00093Q000100044Q004C00012Q0099010700043Q001243000800194Q008B010900014Q00260107000900012Q009901076Q004801085Q00202Q00080008001800202Q00080008000500102Q0007001800084Q00075Q00202Q000700070018000E2Q001A00850001000700044F3Q008500012Q0099010700043Q0012730108001B6Q0007000200014Q000700063Q00122Q0008001A6Q0007000200016Q00013Q00044Q008500010026DF3Q00850001001A00044F3Q008500010006080104008500013Q00044F3Q008500012Q0099010500053Q00204D01050005001C0026DF0005006A0001001D00044F3Q006A00012Q0099010500053Q00204D01050005001E2Q008C010500053Q00060D0105006C0001000100044F3Q006C00012Q0099010500053Q00204D01050005001E00204D01060004000F0012DB0007001F3Q00202Q00070007001600122Q000800076Q000900053Q00122Q000A00076Q0007000A00024Q00060006000700122Q000700153Q00202Q0007000700164Q000800066Q00070002000200102Q0002001500074Q00075Q00302Q0007000600204Q00075Q00302Q0007001800074Q000700043Q00122Q0008000A3Q00202Q00080008000B00122Q000900216Q000A5Q00202Q000A000A000D4Q0008000A6Q00073Q00012Q009901055Q00126E000600223Q00202Q0006000600234Q00075Q00202Q00070007000D00202Q00070007000E4Q00060002000200102Q0005000D00066Q00017Q00213Q00030E3Q00537475636B446574656374696F6E03073Q00456E61626C6564030B3Q0043752Q72656E74526F636B03063Q00506172656E74030A3Q004C617374526F636B485000030B3Q004C617374526F636B52656603123Q004D696E657353696E636548504368616E6765028Q00030E3Q00537475636B436865636B54696D65030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D6503113Q00506F736974696F6E5468726573686F6C6403153Q00506F736974696F6E436865636B496E74657276616C03043Q007469636B03083Q00506F736974696F6E03093Q004D61676E697475646503103Q004C6173745265636F7665727954696D6503103Q005265636F76657279432Q6F6C646F776E03063Q00737472696E6703063Q00666F726D617403293Q00732C3F20535455434B20504F533A206D6F76656420252E3266203C20252E326620696E20252E316673026Q00F03F030D3Q005265636F766572794C6576656C030E3Q004C32412Q74656D7074436F756E74030D3Q0054696D655468726573686F6C64027Q0040024Q007E842E41030B3Q005468726573686F6C644C33026Q000840030B3Q005468726573686F6C644C32026Q00F83F030B3Q005468726573686F6C644C3100D74Q0099016Q00204D014Q0001000608012Q000900013Q00044F3Q000900012Q0099016Q00204D014Q000100204D014Q000200060D012Q000A0001000100044F3Q000A00012Q0064012Q00014Q0099012Q00013Q00204D014Q0003000608012Q001100013Q00044F3Q0011000100204D2Q013Q000400060D2Q01001E0001000100044F3Q001E00012Q00992Q0100013Q0030200001000500064Q000100013Q00302Q0001000700064Q000100013Q00302Q0001000800094Q000100013Q00302Q0001000A00094Q000100013Q00302Q0001000B00064Q000100013Q00302Q0001000C00096Q00014Q00992Q0100024Q000B0001000100024Q000200036Q000300016Q0002000200024Q00035Q00202Q00030003000100062Q0002005E00013Q00044F3Q005E000100204D01040003000D0006080104005E00013Q00044F3Q005E000100204D01040003000E0006080104005E00013Q00044F3Q005E00010012690104000F4Q00030004000100022Q0099010500013Q00204D01050005000C00060D010500340001000100044F3Q00340001001243000500094Q007901050004000500204D01060003000E0006F40006005E0001000500044F3Q005E00012Q0099010500013Q00204D01050005000B0006080105005900013Q00044F3Q0059000100204D0105000200102Q0099010600013Q00204D01060006000B2Q007901050005000600204D01050005001100204D01060003000D00067A000500590001000600044F3Q005900012Q0099010600013Q00204D0106000600122Q007901060004000600204D0107000300130006F4000700590001000600044F3Q005900012Q0099010600043Q001293010700143Q00202Q00070007001500122Q000800166Q000900053Q00202Q000A0003000D00202Q000B0003000E4Q0007000B00024Q000800016Q0006000800014Q000600053Q00122Q000700176Q0006000200014Q000600013Q00102Q0006000A00042Q0099010500013Q00204D0106000200100010E10005000B00062Q0099010500013Q0010E10005000C00042Q00992Q0100064Q00B400028Q00010002000200122Q0002000F6Q0002000100024Q000300013Q00202Q00030003000700062Q0003007800013Q00044F3Q007800012Q0099010300013Q0010850103000500014Q000300013Q00102Q000300076Q000300013Q00302Q0003000800094Q000300013Q00102Q0003000A00024Q000300013Q00302Q0003001800094Q000300013Q00302Q0003001900094Q000300013Q00302Q0003000B00064Q000300013Q00102Q0003000C00026Q00013Q00060D2Q01008A0001000100044F3Q008A00012Q0099010300013Q00204D01030003000A00060D0103007F0001000100044F3Q007F00012Q0090010300024Q00790103000200032Q005301045Q00202Q00040004000100202Q00040004001A00202Q00040004001B00062Q000400890001000300044F3Q008900012Q0099010400053Q001243000500174Q007B0104000200012Q0064012Q00014Q0099010300013Q00204D01030003000500060D0103008F0001000100044F3Q008F00010012430003001C3Q00067A000100A20001000300044F3Q00A200012Q0099010300013Q0010D90003000500014Q000300013Q00302Q0003000800094Q000300013Q00102Q0003000A00024Q000300013Q00302Q0003001800094Q000300013Q00302Q00030019000900262Q000100A10001000900044F3Q00A100012Q0099010300013Q00306D0003000500062Q0099010300013Q00306D0003000700062Q0064012Q00014Q0099010300014Q0046000400013Q00202Q00040004000800202Q00040004001700102Q0003000800044Q000300013Q00202Q00030003000A4Q0003000200034Q000400013Q00202Q0004000400124Q0004000200044Q00055Q00202Q00050005000100202Q00050005001300062Q000400B30001000500044F3Q00B300012Q0064012Q00014Q009901045Q0020570004000400014Q000500013Q00202Q00050005000800202Q00060004001D00062Q000600BE0001000500044F3Q00BE00012Q0099010500053Q0012430006001E4Q007B01050002000100044F3Q00D600012Q0099010500013Q00204D01050005000800204D01060004001F00065C010600050001000500044F3Q00C7000100204D01050004001A0020160105000500200006F4000500CB0001000300044F3Q00CB00012Q0099010500053Q0012430006001B4Q007B01050002000100044F3Q00D600012Q0099010500013Q00204D01050005000800204D01060004002100065C010600040001000500044F3Q00D3000100204D01050004001A0006F4000500D60001000300044F3Q00D600012Q0099010500053Q001243000600174Q007B0105000200012Q0064012Q00017Q00093Q0003043Q007479706503063Q00737472696E6703053Q007461626C6503043Q005465787403073Q004D652Q7361676503073Q00436F6E74656E7403043Q007465787403073Q006D652Q7361676503073Q00636F6E74656E74011F3Q0012692Q0100014Q009001026Q00310001000200020026DF000100060001000200044F3Q000600012Q00E23Q00023Q0012692Q0100014Q009001026Q00310001000200020026DF0001001C0001000300044F3Q001C000100204D2Q013Q000400060D2Q01001B0001000100044F3Q001B000100204D2Q013Q000500060D2Q01001B0001000100044F3Q001B000100204D2Q013Q000600060D2Q01001B0001000100044F3Q001B000100204D2Q013Q000700060D2Q01001B0001000100044F3Q001B000100204D2Q013Q000800060D2Q01001B0001000100044F3Q001B000100204D2Q013Q00092Q00E2000100024Q001A2Q0100014Q00E2000100024Q0064012Q00017Q00103Q0003053Q007063612Q6C03043Q006D6174682Q033Q006D696E026Q00F03F026Q00144003363Q002043612Q6E6F742066696E64204E6F74696669636174696F6E536572766963652E52452E4E6F74696679202D20726574727920696E2003013Q007303043Q007461736B03053Q0064656C61792Q033Q00497341030B3Q0052656D6F74654576656E74033E3Q00204E6F74696669636174696F6E536572766963652E4E6F74696679206973206E6F742052656D6F74654576656E74202D20682Q6F6B2064697361626C6564028Q00030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637403193Q00204E6F74696669636174696F6E20482Q6F6B2041435449564500444Q0099016Q000608012Q000400013Q00044F3Q000400012Q0064012Q00013Q001269012Q00013Q0006822Q013Q000100012Q0099012Q00014Q001C3Q00020001000608012Q000C00013Q00044F3Q000C000100060D2Q0100230001000100044F3Q00230001001269010200023Q00204D0102000200032Q0099010300023Q00207D000300030004001243000400054Q00440002000400022Q0097010200024Q0099010200024Q0099010300033Q001243000400064Q0090010500023Q001243000600074Q001F0104000400064Q000500016Q00030005000100122Q000300083Q00202Q0003000300094Q000400023Q00068201050001000100022Q0099012Q00044Q0099012Q00054Q00260103000500012Q0064012Q00013Q00201801020001000A0012430004000B4Q004400020004000200060D0102002D0001000100044F3Q002D00012Q0099010200033Q0012430003000C4Q008B010400014Q00260102000400012Q0064012Q00013Q0012430002000D4Q0097010200023Q00204D01020001000E00201801020002000F000682010400020001000B2Q0099012Q00064Q0099012Q00074Q0099012Q00084Q0099012Q00044Q0099012Q00094Q0099012Q000A4Q0099012Q000B4Q0099012Q000C4Q0099012Q000D4Q0099012Q000E4Q0099012Q00034Q00870102000400024Q00028Q000200033Q00122Q000300106Q000400016Q0002000400016Q00013Q00033Q00073Q0003063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q00536572766963657303133Q004E6F74696669636174696F6E5365727669636503023Q00524503063Q004E6F74696679000A4Q00DC7Q00206Q000100206Q000200206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00013Q00030A3Q004175746F4D696E696E6700074Q0099016Q00204D014Q0001000608012Q000600013Q00044F3Q000600012Q0099012Q00014Q00A43Q000100012Q0064012Q00017Q00183Q0003053Q006C6F77657203043Q006773756203043Q003C2E2D3E034Q0003043Q0066696E64030E3Q00616C7265616479206D696E696E6703043Q007469636B03153Q004C617374416C72656164794D696E696E6754696D65030B3Q0043752Q72656E74526F636B030A3Q004175746F4D696E696E6703083Q00506F736974696F6E03093Q004D61676E6974756465030C3Q0043752Q72656E745068617365026Q00104003083Q0044697374616E6365026Q002040027Q0040030C3Q00536B692Q706564526F636B73030D3Q0050656E64696E675377697463682Q0103073Q00556E6B6E6F776E03063Q00737472696E6703063Q00666F726D6174032E3Q0020414C5245414459204D494E494E47207C20526F636B3A202573207C2050656E64696E67207377697463683Q2E01614Q00992Q016Q009001026Q003100010002000200060D2Q0100060001000100044F3Q000600012Q0064012Q00013Q0020180102000100012Q00A401020002000200202Q00020002000200122Q000400033Q00122Q000500046Q00020005000200202Q00030002000500122Q000500066Q00030005000200062Q000300120001000100044F3Q001200012Q0064012Q00013Q001269010300074Q00030003000100022Q0099010400013Q00204D0104000400082Q00790104000300042Q0099010500023Q00067A0004001B0001000500044F3Q001B00012Q0064012Q00014Q0099010400013Q00204D0104000400090006080104002300013Q00044F3Q002300012Q0099010400033Q00204D01040004000A00060D010400240001000100044F3Q002400012Q0064012Q00014Q0099010400044Q00980004000100024Q000500056Q000600046Q0005000200024Q000600066Q000700013Q00202Q0007000700094Q00060002000200062Q0005003100013Q00044F3Q0031000100060D010600320001000100044F3Q003200012Q0064012Q00013Q00204D01070006000B0020A201080005000B4Q00070007000800202Q00070007000C4Q000800013Q00202Q00080008000D00262Q0008003B0001000E00044F3Q003B00012Q0064012Q00014Q0099010800033Q00204D01080008000F00207D00080008001000067A000800410001000700044F3Q004100012Q0064012Q00014Q0099010800074Q0079010800030008000ED5001100460001000800044F3Q004600012Q0064012Q00014Q0099010800013Q0010E10008000800032Q0099010800013Q00204D0108000800122Q0099010900013Q00204D0109000900092Q0099010A00084Q0062000A0003000A2Q007B00080009000A2Q0099010800013Q00306D0008001300142Q00EB000800096Q000900013Q00202Q0009000900094Q00080002000200062Q000800580001000100044F3Q00580001001243000800154Q00990109000A3Q00127A010A00163Q00202Q000A000A001700122Q000B00186Q000C00086Q000A000C00024Q000B00016Q0009000B00016Q00017Q00033Q00030A3Q00446973636F2Q6E656374031F3Q00204E6F74696669636174696F6E20482Q6F6B20444953434F2Q4E4543544544029Q000E4Q0099016Q000608012Q000B00013Q00044F3Q000B00012Q0099016Q002018014Q00012Q007B012Q000200012Q001A017Q0097017Q0099012Q00013Q001243000100024Q007B012Q000200010012433Q00034Q0097012Q00024Q0064012Q00017Q00103Q0003043Q007469636B03043Q006D6174682Q033Q006D617803093Q004D696E6544656C6179029A5Q99B93F029A5Q99A93F030F3Q004D696E6544656C61794A692Q746572028Q0003063Q0072616E646F6D026Q00F03F03063Q00737472696E6703063Q00666F726D617403183Q00204D696E6520232564202844656C61793A20252E3266732903053Q007063612Q6C03153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C003F3Q001291012Q00018Q0001000200122Q000100023Q00202Q0001000100034Q00025Q00202Q00020002000400062Q000200090001000100044F3Q00090001001243000200053Q001243000300064Q0044000100030002001269010200023Q00204D0102000200032Q009901035Q00204D01030003000700060D010300120001000100044F3Q00120001001243000300083Q001243000400084Q00A901020004000200122Q000300023Q00202Q0003000300094Q0003000100024Q0003000300024Q0003000100034Q000400016Q00043Q000400062Q0004001E0001000300044F3Q001E00012Q0064012Q00014Q0099010400023Q00207D00040004000A2Q0097010400024Q0097012Q00014Q0099010400033Q0012690105000B3Q00204D01050005000C0012430006000D4Q0099010700024Q0090010800034Q00CB000500084Q00B600043Q00010012690104000E3Q00068201053Q000100012Q0099012Q00044Q007B0104000200012Q0099010400054Q00030004000100020006080104003C00013Q00044F3Q003C000100201801050004000F001243000700104Q00440005000700020006080105003B00013Q00044F3Q003B00010012690106000E3Q00068201070001000100012Q0090012Q00054Q007B0106000200012Q005800056Q0099010500064Q00A40005000100012Q0064012Q00013Q00023Q00093Q0003063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q005365727669636573030B3Q00542Q6F6C5365727669636503023Q005246030D3Q00542Q6F6C416374697661746564030C3Q00496E766F6B6553657276657203073Q005069636B617865000C4Q003B7Q00206Q000100206Q000200206Q000300206Q000400206Q000500202Q00013Q000600202Q00010001000700202Q00010001000800122Q000300094Q00262Q01000300012Q0064012Q00017Q00013Q0003083Q00416374697661746500044Q0099016Q002018014Q00012Q007B012Q000200012Q0064012Q00017Q000A3Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C030E3Q0046696E6446697273744368696C6403083Q004261636B7061636B03053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103083Q0048756D616E6F696403093Q004571756970542Q6F6C002D4Q0099017Q00033Q0001000200060D012Q00050001000100044F3Q000500012Q0064012Q00013Q00204D2Q013Q00010006082Q01000D00013Q00044F3Q000D0001002018010200010002001243000400034Q00440002000400020006080102000E00013Q00044F3Q000E00012Q0064012Q00013Q00201801023Q0004001243000400054Q004400020004000200060D010200140001000100044F3Q0014000100204D01023Q000500060D010200170001000100044F3Q001700012Q0064012Q00013Q001269010300063Q0020180104000200072Q0041000400054Q002201033Q000500044F3Q002A0001002018010800070008001243000A00034Q00440008000A00020006080108002A00013Q00044F3Q002A0001002018010800010004001243000A00094Q00440008000A00020006080108002900013Q00044F3Q0029000100201801090008000A2Q0090010B00074Q00260109000B00012Q0064012Q00013Q0006AA0003001C0001000200044F3Q001C00012Q0064012Q00017Q00163Q00032F3Q00204D616769632043617270657420616C7265616479206578697374732C20736B692Q70696E67206372656174696F6E03083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503113Q004D696E696E674D6167696343617270657403043Q0053697A6503073Q00566563746F7233026Q001840026Q00E03F030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C696465010003083Q0043616E546F75636803083Q0043616E517565727903063Q00506172656E74034A3Q00204D61676963204361727065742043524541544544207C2053697A653A203678302E357836207C20416E63686F7265643A2074727565207C2043616E436F2Q6C6964653A2066616C736503053Q007072696E74032C3Q005B466F726765204D696E696E675D204D61676963204361727065742043726561746564202853746174696329002B4Q0099016Q000608012Q000700013Q00044F3Q000700012Q0099012Q00013Q001243000100014Q007B012Q000200012Q0064012Q00013Q001269012Q00023Q00204D014Q0003001243000100044Q00313Q000200022Q0097017Q0099016Q00306D3Q000500062Q0099016Q0012692Q0100083Q00204D2Q0100010003001243000200093Q0012430003000A3Q001298010400096Q00010004000200104Q000700019Q0000304Q000B000C9Q0000304Q000D000E9Q0000304Q000F00109Q0000306D3Q001100102Q003F7Q00304Q001200109Q004Q000100023Q00104Q001300016Q00013Q00122Q000100146Q000200018Q0002000100124Q00153Q001243000100164Q007B012Q000200012Q0064012Q00017Q00133Q0003063Q00434672616D652Q033Q006E6577028Q00030B3Q0047686F73744F2Q6673657403063Q00506172656E7403083Q0043616E546F75636803083Q0043616E5175657279010003093Q0044656275674D6F646503043Q006D61746803063Q0072616E646F6D027B14AE47E17A943F03083Q00506F736974696F6E03063Q00737472696E6703063Q00666F726D617403373Q004D616769632043617270657420757064617465643A2028252E31662C20252E31662C20252E316629207C204F2Q667365743A20252E316603013Q005803013Q005903013Q005A013D3Q00060D012Q00030001000100044F3Q000300012Q0064012Q00014Q00992Q015Q00060D2Q0100080001000100044F3Q000800012Q00992Q0100014Q00A400010001000100204D2Q013Q0001001269010200013Q00204D010200020002001243000300034Q0099010400023Q00204D010400040004001243000500034Q00440002000500022Q00682Q01000100022Q009901025Q00204D0102000200052Q0099010300033Q0006A7000200190001000300044F3Q001900012Q009901026Q0099010300033Q0010E10002000500032Q009901025Q00204D01020002000600060D010200210001000100044F3Q002100012Q009901025Q00204D0102000200070006080102002500013Q00044F3Q002500012Q009901025Q00306D0002000600082Q009901025Q00306D0002000700082Q009901025Q0010E10002000100012Q0099010200023Q00204D0102000200090006080102003C00013Q00044F3Q003C00010012690102000A3Q00204D01020002000B2Q00030002000100020026240102003C0001000C00044F3Q003C000100204D01020001000D2Q0042000300043Q00122Q0004000E3Q00202Q00040004000F00122Q000500103Q00202Q00060002001100202Q00070002001200202Q0008000200134Q000900023Q00202Q0009000900044Q000400096Q00033Q00012Q0064012Q00017Q00043Q0003073Q0044657374726F7903163Q004D61676963204361727065742044455354524F59454403053Q007072696E7403253Q005B466F726765204D696E696E675D204D61676963204361727065742044657374726F79656400104Q0099016Q000608012Q000F00013Q00044F3Q000F00012Q0099016Q0020BC5Q00016Q000200019Q009Q006Q00013Q00122Q000100026Q000200018Q0002000100124Q00033Q00122Q000100048Q000200012Q0064012Q00017Q00143Q0003163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030D3Q00506C6174666F726D5374616E64010003043Q004865616403053Q00546F72736F030A3Q00552Q706572546F72736F030A3Q004C6F776572546F72736F03053Q0070616972732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103053Q007072696E7403463Q005B4D696E696E675D20436C65616E7570506879736963733A20506C6174666F726D5374616E643D66616C73652C2043616E436F2Q6C6964653D7472756520726573746F72656403073Q0044657374726F79003B4Q0099017Q00033Q00010002000608012Q003200013Q00044F3Q003200012Q00992Q0100014Q009001026Q00310001000200020006082Q01000F00013Q00044F3Q000F0001001269010200023Q00204401020002000300102Q00010001000200122Q000200023Q00202Q00020002000300102Q00010004000200201801023Q0005001243000400064Q00440002000400020006080102001800013Q00044F3Q0018000100204D0103000200070006080103001800013Q00044F3Q0018000100306D0002000700082Q006D010300043Q0012DA000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q0007000C6Q0003000400010012690104000D4Q0090010500034Q001C00040002000600044F3Q002D000100201801093Q00052Q0090010B00084Q00440009000B00020006080109002D00013Q00044F3Q002D0001002018010A0009000E001243000C000F4Q0044000A000C0002000608010A002D00013Q00044F3Q002D000100306D0009001000110006AA000400220001000200044F3Q00220001001269010400123Q001243000500134Q007B0104000200012Q00992Q0100023Q0006082Q01003A00013Q00044F3Q003A00012Q00992Q0100023Q0020182Q01000100142Q007B2Q01000200012Q001A2Q0100014Q00972Q0100024Q0064012Q00017Q00033Q0003073Q0044657374726F79030A3Q00446973636F2Q6E65637403163Q002046752Q6C20436C65616E757020436F6D706C65746500394Q00C99Q003Q000100016Q00018Q000100016Q00023Q00064Q000C00013Q00044F3Q000C00012Q0099012Q00023Q002018014Q00012Q007B012Q000200012Q001A017Q0097012Q00024Q0099012Q00033Q000608012Q001400013Q00044F3Q001400012Q0099012Q00033Q002018014Q00022Q007B012Q000200012Q001A017Q0097012Q00034Q0099012Q00043Q000608012Q001C00013Q00044F3Q001C00012Q0099012Q00043Q002018014Q00022Q007B012Q000200012Q001A017Q0097012Q00044Q0099012Q00054Q00992Q0100064Q00313Q00020002000608012Q002600013Q00044F3Q002600012Q0099012Q00063Q002018014Q00022Q007B012Q000200012Q001A017Q0097012Q00064Q0099012Q00054Q00992Q0100074Q00313Q00020002000608012Q003000013Q00044F3Q003000012Q0099012Q00073Q002018014Q00022Q007B012Q000200012Q001A017Q0097012Q00074Q008B017Q003A012Q00088Q00098Q000100016Q000A3Q00122Q000100036Q000200018Q000200016Q00017Q001A3Q0003123Q004D61696E74656E616E6365456E61626C656403043Q007469636B03103Q0053652Q73696F6E537461727454696D65028Q0003133Q004C6173744D61696E74656E616E636554696D6503133Q004D61696E74656E616E6365496E74657276616C03183Q004D61696E74656E616E63654D696E655468726573686F6C64024Q008087C34003103Q004D61696E74656E616E6365436F756E74026Q00F03F03063Q00737472696E6703063Q00666F726D617403293Q00204D41494E54454E414E434520232564207C20557074696D653A202573207C204D696E65643A202564030A3Q00546F74616C4D696E6564030E3Q004C6173744C2Q6F6B54617267657400030D3Q0050656E64696E67537769746368010003113Q004C61737450656E64696E67537769746368030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B7303063Q006763696E666F026Q004E4003163Q00204D616769634361727065742052454652455348454403073Q0044657374726F7903483Q00204D61696E74656E616E636520436F6D706C657465207C204D696E65732072657365743A2025642D3E30207C204D656D6F72793A20252E3166204B42207C204D504D3A20252E316600754Q0099016Q00204D014Q000100060D012Q00050001000100044F3Q000500012Q0064012Q00013Q001269012Q00024Q00033Q000100022Q00992Q0100013Q00204D2Q01000100030026DF0001000C0001000400044F3Q000C00012Q0064012Q00014Q00992Q0100013Q0020812Q01000100054Q00013Q00014Q00025Q00202Q00020002000600062Q000200020001000100044F3Q001400012Q00EF00016Q008B2Q0100014Q0099010200024Q009901035Q00204D01030003000700060D0103001B0001000100044F3Q001B0001001243000300083Q00065C010300020001000200044F3Q001E00012Q00EF00026Q008B010200013Q00060D2Q0100240001000100044F3Q0024000100060D010200240001000100044F3Q002400012Q0064012Q00014Q0099010300014Q00D7000400013Q00202Q00040004000900202Q00040004000A00102Q0003000900044Q000300013Q00102Q000300056Q000300036Q000400013Q00202Q0004000400034Q00043Q00044Q0003000200024Q000400043Q00122Q0005000B3Q00202Q00050005000C00122Q0006000D6Q000700013Q00202Q0007000700094Q000800036Q000900013Q00202Q00090009000E4Q0005000900024Q000600016Q0004000600014Q000400023Q00122Q000500046Q000500026Q000500013Q00302Q0005000F00104Q000500013Q00302Q0005001100124Q000500013Q00302Q0005001300044Q000500016Q00065Q00102Q0005001400064Q000500016Q00065Q00102Q00050015000600122Q000500166Q00050001000200122Q000600046Q000700013Q00202Q000700070003000E2Q0004005B0001000700044F3Q005B00012Q0099010700013Q00204D0107000700032Q007901073Q000700200C010700070017000ED50004005B0001000700044F3Q005B00012Q0099010800013Q00204D01080008000E2Q00A00106000800072Q0099010700054Q00DD0007000100014Q000700066Q0007000100014Q000700043Q00122Q000800186Q0007000200014Q000700073Q00062Q0007006A00013Q00044F3Q006A00012Q0099010700073Q0020180107000700192Q007B0107000200012Q001A010700074Q0097010700074Q0099010700043Q0012CA0008000B3Q00202Q00080008000C00122Q0009001A6Q000A00046Q000B00056Q000C00066Q0008000C00024Q000900016Q0007000900016Q00017Q000A3Q0003063Q0048656967687403083Q00506F736974696F6E030A3Q00466C696768744D6F646503053Q0041626F766503013Q0059025Q00207CC003073Q00566563746F72332Q033Q006E657703013Q005803013Q005A01184Q00052Q015Q00202Q00010001000100202Q00023Q00024Q000300036Q00045Q00202Q00040004000300262Q0004000B0001000400044F3Q000B000100204D0104000200052Q006200030004000100044F3Q000D000100204D0104000200052Q0079010300040001002624010300100001000600044F3Q00100001001243000300063Q001269010400073Q00204D01040004000800204D0105000200092Q0090010600033Q00204D01070002000A2Q002C000400074Q002101046Q0064012Q00017Q007C3Q0003083Q00506F736974696F6E03243Q0020504F534954494F4E204953204E614E212041626F7274696E67206D6F76656D656E742E03103Q00486F72697A6F6E74616C4F2Q6673657403043Q006D6174682Q033Q00616273028Q0003073Q00566563746F72332Q033Q006E657703013Q005803013Q005A03093Q004D61676E6974756465023Q00E04D62503F03043Q00556E6974030A3Q0047686F737453702Q6564026Q11913F030C3Q0043752Q72656E745068617365027Q0040026Q000840026Q001040026Q00344003133Q00446972656374436861736544697374616E636503013Q0059026Q001440026Q00F03F030D3Q00506C6174666F726D5374616E642Q0102CD5QCCF43F03063Q00737472696E6703063Q00666F726D617403313Q0020444952454354204348415345207C20646973743A252E3166203C202564207C20736B692Q70696E672050686173652031026Q002440026Q003E40034Q00030F3Q0050313A4845494748545F434845434B030C3Q0050323A524F434B5F474F4E4503123Q0020526F636B206D6F7665642120666C61743D03053Q00666C2Q6F72030A3Q002Q2043686173696E672103123Q0050333A485953544552455349535F4C4F434B026Q002E4003113Q0050343A4E4F545F504F534954494F4E4544030D3Q0050353A564552595F434C4F5345030F3Q0050353A4E4F524D414C5F454E545259030E3Q0050353A4B2Q45505F4445504C4F5903063Q0072616E646F6D029A5Q99A93F03013Q004E03323Q00205048415345207C2025642564207C20666C61743A252E316620646973743A252E3166207C20776173343A2573207C20257303163Q00412Q73656D626C794C696E65617256656C6F6369747903043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q004C6F636B65644D696E65506F7300030D3Q0053702Q6564412Q70726F616368030E3Q00536B69704D696E654672616D657303083Q0044697374616E6365030F3Q004F7265436865636B456E61626C6564030B3Q0043752Q72656E74526F636B03073Q00556E6B6E6F776E03103Q004C61737446696C746572536F75726365030E3Q004C61737446696C746572526F636B032F3Q00204F52452046494C54455220534F55524345207C202573207C205573696E672025732066696C7465723A205B25735D03053Q007461626C6503063Q00636F6E63617403023Q002C20030D3Q004F7265436865636B4C6576656C030F3Q004F7265536B69704E6F74696669656403043Q007469636B2Q033Q006E696C03343Q00204F524520434845434B207C20526F636B3A202573207C204C6576656C3A2025642Q25207C20412Q4C204F7265733A205B25735D03063Q0069706169727303083Q00746F737472696E6703053Q006C6F77657203363Q002046494C54455220434845434B207C204F7265733A205B25735D2076732046696C7465723A205B25735D207C204D617463683A20257303063Q00594553202D2003013Q003F03023Q004E4F03103Q004F726546696C7465726564526F636B7303133Q004F726520536B697020284D69736D6174636829034D3Q0020534B495020524F434B207C202725732720686173206F726573205B25735D206275742066696C7465722077616E7473205B25735D207C204C6576656C3A2025642Q25207C2043443A20256473033D3Q00204F5245204D41544348207C20526F636B202725732720686173205B25735D207C204D6174636865643A2027257327207C204C6576656C3A2025642Q25030C3Q004D617463686564526F636B73030D3Q004F7265536B69704E6F74696679032B3Q00E29C8520257320402025642Q250AF09F928E204861733A2025730AF09F8EAF204D6174636865643A20257303053Q005469746C65030E3Q00E29C85204F7265204D617463682103073Q00436F6E74656E7403083Q004475726174696F6E026Q00204003113Q004F726520536B697020284E6F204F726529033C3Q00204F5245204E494C207C20526F636B20272573272061742025642Q2520686173206E6F204F726520612Q7472696275746521207C2043443A2025647303093Q0044656275674D6F6465027B14AE47E17A943F03313Q0020542Q4F2046415220544F204D494E45207C20646973743A252E3166203E20436F6E6669672E44697374616E63653A256402B81E85EB51B89E3F030D3Q0053616665747920417363656E74030A3Q00536B7920437275697365030A3Q004465706C6F796D656E7403063Q004D696E696E67032A3Q002050686173652025643A202573207C20446973743A20252E3166207C20593A20252E31662Q20252E3166029A5Q99B93F03093Q0053702Q65644E656172030B3Q0053702Q6564536C6F776D6F026Q00494003083Q0053702Q65644661722Q033Q006D696E03083Q00496E7374616E636503083Q00426F64794779726F03093Q004D6178546F72717565024Q00652QCD4103013Q0050025Q0088C34003013Q0044026Q00594003063Q00506172656E7403143Q004C61737454726176656C4C2Q6F6B546172676574030E3Q004C6173744C2Q6F6B54617267657403103Q00526F746174696F6E446561645A6F6E6503063Q00434672616D6503063Q006C2Q6F6B4174030A3Q004C2Q6F6B566563746F7203453Q0020524F544154494F4E207C2046752Q6C334420617420726F636B207C20446973743A20252E3166207C204C2Q6F6B5665633A2028252E32662C20252E32662C20252E32662903043Q006875676503163Q00526F746174696F6E446561645A6F6E6554726176656C0458033Q00C300048Q00058Q00040002000100202Q00043Q000100202Q0005000200014Q000600016Q000700046Q00060002000200062Q0006000F00013Q00044F3Q000F00012Q0099010600014Q0090010700054Q003100060002000200060D010600140001000100044F3Q001400012Q0099010600023Q001243000700024Q008B010800014Q00260106000800012Q0064012Q00014Q0099010600034Q005A000700026Q0006000200024Q000700046Q000800046Q0007000200024Q000800053Q00202Q00080008000300062Q0008003E00013Q00044F3Q003E0001001269010800043Q00204D0108000800052Q0099010900053Q00204D0109000900032Q0031000800020002000ED50006003E0001000800044F3Q003E0001001269010800073Q00207801080008000800202Q00090005000900202Q000A000400094Q00090009000A00122Q000A00063Q00202Q000B0005000A00202Q000C0004000A4Q000B000B000C4Q0008000B000200202Q00090008000B000E2Q000C003E0001000900044F3Q003E000100204D01090008000D001281000A00073Q00202Q000A000A000800202Q000B0009000A4Q000B000B3Q00122Q000C00063Q00202Q000D000900094Q000A000D00024Q000B00053Q00202Q000B000B00034Q000B000A000B4Q00060006000B2Q0099010800053Q00204D01080008000E000633010900430001000300044F3Q004300010012430009000F4Q0068010800080009001213010900073Q00202Q00090009000800202Q000A0006000900202Q000B000400094Q000A000A000B00122Q000B00063Q00202Q000C0006000A00202Q000D0004000A4Q000C000C000D4Q0009000C000200204D01090009000B2Q0079010A0006000400204D010A000A000B2Q001A010B000B4Q008B010C5Q001243000D00064Q0099010E00063Q00204D010E000E00100026E5000E00590001001100044F3Q005900012Q00EF000E6Q008B010E00014Q0099010F00063Q00204D010F000F00100026E5000F00630001001200044F3Q006300012Q0099010F00063Q00204D010F000F00100026E5000F00630001001300044F3Q006300012Q00EF000F6Q008B010F00013Q000608010F006B00013Q00044F3Q006B0001000ED50014006B0001000900044F3Q006B00012Q008B010F6Q0099011000063Q00306D0010001000062Q0099011000053Q00204D01100010001500065C010A00020001001000044F3Q007000012Q00EF00106Q008B011000013Q00060D011000890001000100044F3Q0089000100060D010E00890001000100044F3Q0089000100060D010F00890001000100044F3Q0089000100204D0111000400160020A801120007001700067A001100890001001200044F3Q00890001001243000D00183Q001222001100073Q00202Q00110011000800202Q0012000400094Q001300073Q00202Q00140004000A4Q0011001400024Q000B00113Q00202Q00110001001900062Q001100870001000100044F3Q0087000100306D00010019001A00201601080008001B00044F3Q007C0201000608011000A300013Q00044F3Q00A3000100060D010E00A30001000100044F3Q00A3000100060D010F00A30001000100044F3Q00A3000100204D0111000400160020A801120007001700067A001100A30001001200044F3Q00A30001001243000D00124Q0090010B00063Q00204D01110001001900060D011100990001000100044F3Q0099000100306D00010019001A2Q0099011100023Q0012970012001C3Q00202Q00120012001D00122Q0013001E6Q0014000A6Q001500053Q00202Q0015001500154Q001200156Q00113Q000100044Q007C020100060D010E00A90001000100044F3Q00A9000100204D0111000400160020A80112000700170006F4001200C40001001100044F3Q00C40001000ED5001F00C40001000900044F3Q00C4000100060D010F00C40001000100044F3Q00C40001001243000D00114Q0090011100073Q00204D0112000400160020A801130007001700067A001200B40001001300044F3Q00B4000100207D001100070011001269011200073Q00204B01120012000800202Q0013000600094Q001400113Q00202Q00150006000A4Q0012001500024Q000B00123Q00262Q000900BE0001002000044F3Q00BE00012Q00EF000C6Q008B010C00013Q00204D01120001001900060D0112007C0201000100044F3Q007C020100306D00010019001A00044F3Q007C02012Q0099011100063Q00204D0111001100100026E5001100C90001001300044F3Q00C900012Q00EF00116Q008B011100013Q0012B5001200043Q00202Q00120012000500202Q00130004001600202Q0014000600164Q0013001300144Q00120002000200122Q001300133Q00122Q001400213Q00202Q00150004001600202Q00160006001600202Q00160016001F00062Q001500DD0001001600044F3Q00DD000100204D01150004001600204D01160006001600207D00160016001F000600011600DD0001001500044F3Q00DD00012Q00EF00156Q008B011500013Q000608011500E300013Q00044F3Q00E30001001243000D00123Q001243001400223Q00044F3Q00122Q01000608011100F400013Q00044F3Q00F40001000ED5001F00F40001000900044F3Q00F40001001243000D00183Q00123E001400236Q001600023Q00122Q001700243Q00122Q001800043Q00202Q0018001800254Q001900096Q00180002000200122Q001900266Q0017001700194Q001800016Q00160018000100044Q00122Q01000608011100FB00013Q00044F3Q00FB00010026E7000900FB0001001F00044F3Q00FB0001001243000D00133Q001243001400273Q00044F3Q00122Q01000ED5002800022Q01000900044F3Q00022Q0100060D011100022Q01000100044F3Q00022Q01001243000D00123Q001243001400293Q00044F3Q00122Q01002624010900072Q01001800044F3Q00072Q01001243000D00133Q0012430014002A3Q00044F3Q00122Q01000608010F00102Q013Q00044F3Q00102Q01002624010900102Q01001700044F3Q00102Q0100067A000A00102Q01001300044F3Q00102Q01001243000D00133Q0012430014002B3Q00044F3Q00122Q01001243000D00123Q0012430014002C4Q0099011600063Q00204D011600160010000618000D001B2Q01001600044F3Q001B2Q01001269011600043Q00204D01160016002D2Q00030016000100020026240116002E2Q01002E00044F3Q002E2Q01000608011100202Q013Q00044F3Q00202Q01001243001600163Q00060D011600212Q01000100044F3Q00212Q010012430016002F4Q0099011700023Q0012090018001C3Q00202Q00180018001D00122Q001900306Q001A00063Q00202Q001A001A00104Q001B000D6Q001C00096Q001D000A6Q001E00166Q001F00144Q00CB0018001F4Q00B600173Q00010026DF000D00760201001300044F3Q00760201001269011600073Q00204401160016003200104Q0031001600122Q001600073Q00202Q00160016003200104Q00330016002624010A00412Q01001100044F3Q00412Q012Q0099011600063Q00204D01160016003400060D0116003E2Q01000100044F3Q003E2Q012Q0099011600063Q0010E10016003400042Q0099011600063Q00204D010B0016003400044F3Q00472Q012Q0099011600063Q0030480016003400354Q000B00066Q001600053Q00202Q0016001600364Q00080008001600204D01160001001900060D0116004B2Q01000100044F3Q004B2Q0100306D00010019001A2Q0099011600063Q00204D011600160037000ED5000600552Q01001600044F3Q00552Q012Q0099011600064Q00A3001700063Q00202Q00170017003700202Q00170017001800102Q00160037001700044Q007B02012Q0099011600053Q00204D01160016003800207D0016001600130006F4000A00630201001600044F3Q006302012Q0099011600053Q00204D0116001600390006080116006002013Q00044F3Q006002012Q0099011600063Q00204D01160016003A0006080116006002013Q00044F3Q006002012Q0099011700074Q0090011800164Q003100170002000200060D011700682Q01000100044F3Q00682Q010012430017003B4Q0099011800084Q0090011900174Q001C001800020019000608011900892Q013Q00044F3Q00892Q012Q0099011A00063Q00204D011A001A003C000618001A00752Q01001900044F3Q00752Q012Q0099011A00063Q00204D011A001A003D0006A7001A00892Q01001700044F3Q00892Q012Q0099011A00063Q00104C011A003C00194Q001A00063Q00102Q001A003D00174Q001A00023Q00122Q001B001C3Q00202Q001B001B001D00122Q001C003E6Q001D00176Q001E00193Q00122Q001F003F3Q00202Q001F001F00404Q002000183Q00122Q002100416Q001F00216Q001B8Q001A3Q00014Q001A00096Q001B00176Q001A000200010006080118006002013Q00044F3Q006002012Q0034001A00183Q000ED5000600600201001A00044F3Q006002012Q0099011A000A6Q001B00166Q001A000200024Q001B00053Q00202Q001B001B004200062Q001A00600201001B00044F3Q006002012Q0099011B00063Q00204D011B001B00432Q00C0001B001B001600060D011B00600201000100044F3Q006002012Q0099011B00063Q0020FB001B001B004300122Q001C00446Q001C000100024Q001B0016001C4Q001B000B6Q001C00166Q001B000200024Q001C001B3Q000E2Q000600AC2Q01001C00044F3Q00AC2Q01001269011C003F3Q00204F011C001C00404Q001D001B3Q00122Q001E00416Q001C001E000200062Q001C00AD2Q01000100044F3Q00AD2Q01001243001C00454Q0099011D00023Q0012A1011E001C3Q00202Q001E001E001D00122Q001F00466Q002000176Q0021001A6Q0022001C6Q001E00226Q001D3Q00014Q001D001B3Q000E2Q0006003D0201001D00044F3Q003D02012Q008B011D6Q00A6011E001E3Q00122Q001F00476Q0020001B6Q001F0002002100044Q00D72Q01001269012400484Q005C002500236Q00240002000200202Q0024002400494Q00240002000200122Q002500476Q002600186Q00250002002700044Q00D22Q01001269012A00484Q0086012B00296Q002A0002000200202Q002A002A00494Q002A0002000200062Q002400D22Q01002A00044F3Q00D22Q012Q008B011D00014Q0090011E00233Q00044F3Q00D42Q010006AA002500C82Q01000200044F3Q00C82Q01000608011D00D72Q013Q00044F3Q00D72Q0100044F3Q00D92Q010006AA001F00BF2Q01000200044F3Q00BF2Q01001269011F003F3Q00203A001F001F00404Q002000183Q00122Q002100416Q001F002100024Q002000023Q00122Q0021001C3Q00202Q00210021001D00122Q0022004A6Q0023001C6Q0024001F3Q00062Q001D00ED2Q013Q00044F3Q00ED2Q010012430025004B3Q000633012600EA2Q01001E00044F3Q00EA2Q010012430026004C4Q00ED00250025002600060D012500EE2Q01000100044F3Q00EE2Q010012430025004D4Q00CB002100254Q00B600203Q000100060D011D00130201000100044F3Q00130201001243002000064Q00A0002100063Q00202Q00210021004E00202Q00210016001A4Q0021000C3Q00122Q0022004F6Q002300176Q0024001A6Q0025001C6Q0026001F6Q002700206Q002800166Q0029000D6Q0021002900014Q002100023Q00122Q0022001C3Q00202Q00220022001D00122Q002300506Q002400176Q0025001C6Q0026001F6Q0027001A6Q002800206Q002200286Q00213Q00014Q002100063Q00302Q0021003A00354Q002100063Q00302Q0021001000064Q002100063Q00302Q0021003400356Q00013Q00044Q006002012Q0099012000023Q0012CC0021001C3Q00202Q00210021001D00122Q002200516Q002300176Q0024001C3Q00062Q0025001C0201001E00044F3Q001C02010012430025004C4Q00900126001A4Q0094002100266Q00203Q00014Q002000063Q00202Q00200020005200202Q00200016001A4Q002000053Q00202Q00200020005300062Q0020006002013Q00044F3Q006002012Q00990120000D4Q0090012100164Q00900122000D4Q00440020002200020006080120006002013Q00044F3Q006002010012690120001C3Q00205101200020001D00122Q002100546Q002200176Q0023001A6Q0024001C3Q00062Q002500350201001E00044F3Q003502010012430025004C4Q00440020002500022Q00FF0021000E6Q00223Q000300302Q00220055005600102Q00220057002000302Q0022005800594Q00210002000100044Q00600201001243001D00064Q00F7001E00063Q00202Q001E001E004E00202Q001E0016001A00122Q001E003F3Q00202Q001E001E00404Q001F00183Q00122Q002000416Q001E002000024Q001F000C3Q00122Q0020005A6Q002100176Q0022001A6Q0023001C6Q0024001E6Q0025001D6Q002600166Q0027000D6Q001F002700014Q001F00023Q00122Q0020001C3Q00202Q00200020001D00122Q0021005B6Q002200176Q0023001A6Q0024001D6Q002000246Q001F3Q00014Q001F00063Q00302Q001F003A00354Q001F00063Q00302Q001F001000064Q001F00063Q00302Q001F003400356Q00014Q00990116000F4Q00A400160001000100044F3Q007B02012Q0099011600053Q00204D01160016005C0006080116007B02013Q00044F3Q007B0201001269011600043Q00204D01160016002D2Q00030016000100020026240116007B0201005D00044F3Q007B02012Q0099011600023Q0012970017001C3Q00202Q00170017001D00122Q0018005E6Q0019000A6Q001A00053Q00202Q001A001A00384Q0017001A6Q00163Q000100044Q007B02012Q0090010B00063Q00204D01160001001900060D0116007B0201000100044F3Q007B020100306D00010019001A2Q008B010C00014Q0099011100063Q0010E100110010000D2Q0099011100053Q00204D01110011005C0006080111009C02013Q00044F3Q009C0201001269011100043Q00204D01110011002D2Q00030011000100020026240111009C0201005F00044F3Q009C02012Q006D011100043Q0012DA001200603Q00122Q001300613Q00122Q001400623Q00122Q001500636Q0011000400012Q00C000120011000D00060D011200910201000100044F3Q009102010012430012003B4Q0099011300023Q0012CE0014001C3Q00202Q00140014001D00122Q001500646Q0016000D6Q001700126Q0018000A3Q00202Q00190004001600202Q001A000600164Q0014001A6Q00133Q000100060D010B009F0201000100044F3Q009F02012Q0064012Q00014Q00790111000B000400204D01120011000B000ED5006500A50201001200044F3Q00A5020100204D01110011000D00044F3Q00A602012Q0064012Q00013Q000608010C00B202013Q00044F3Q00B20201002624011200AE0201002800044F3Q00AE02012Q0099011300053Q00204D0113001300662Q006801080008001300044F3Q00B702012Q0099011300053Q00204D0113001300672Q006801080008001300044F3Q00B70201000ED5006800B70201001200044F3Q00B702012Q0099011300053Q00204D0113001300692Q0068010800080013001269011300043Q00207601130013006A4Q001400086Q001500126Q0013001500024Q000800136Q0013001100084Q0013000400134Q001400103Q00062Q001400D50201000100044F3Q00D502010012690114006B3Q00208C00140014000800122Q0015006C6Q0014000200024Q001400106Q001400103Q00122Q001500073Q00202Q00150015000800122Q0016006E3Q00122Q0017006E3Q00122Q0018006E6Q00150018000200102Q0014006D00154Q001400103Q00302Q0014006F00704Q001400103Q00302Q0014007100724Q001400103Q00102Q001400733Q0026DF000D001A0301001300044F3Q001A03012Q0099011400063Q0030C70014007400354Q001400103Q00122Q001500073Q00202Q00150015003200102Q0014006D00154Q001400103Q00302Q0014006F00064Q00140005001300202Q00140014000B000E2Q006500140301001400044F3Q001403012Q0099011500063Q00204D01150015007500060D011500E80201000100044F3Q00E802012Q0090011500054Q007901160005001500209F01160016000B4Q001700176Q001800053Q00202Q00180018007600062Q001800F30201001600044F3Q00F302012Q0099011800063Q00204D01180018007500060D011800F70201000100044F3Q00F702012Q0099011800063Q0010E10018007500052Q0090011700053Q00044F3Q00F802012Q0090011700153Q001269011800773Q00207C0018001800784Q001900136Q001A00176Q0018001A000200104Q007700184Q001800053Q00202Q00180018005C00062Q0018005103013Q00044F3Q00510301001269011800043Q00204D01180018002D2Q0003001800010002002624011800510301002E00044F3Q0051030100204D01183Q00770020BD0018001800794Q001900023Q00122Q001A001C3Q00202Q001A001A001D00122Q001B007A6Q001C00143Q00202Q001D0018000900202Q001E0018001600202Q001F0018000A4Q001A001F4Q00B600193Q000100044F3Q00510301001269011500773Q0020AF0015001500084Q001600136Q00150002000200104Q0077001500044Q00510301001269011400073Q00201C01140014000800202Q0015000B000900202Q00160013001600202Q0017000B000A4Q0014001700024Q00150014001300202Q00150015000B000E2Q006500400301001500044F3Q004003012Q0099011600063Q00204D0116001600740006080116002E03013Q00044F3Q002E03012Q0099011600063Q00204D0116001600742Q007901160014001600204D01160016000B00060D011600300301000100044F3Q00300301001269011600043Q00204D01160016007B2Q0099011700053Q00204D01170017007C00060D011700350301000100044F3Q00350301001243001700063Q00067A001700400301001600044F3Q004003012Q0099011700103Q0012AB001800773Q00202Q0018001800784Q001900136Q001A00146Q0018001A000200102Q0017007700184Q001700063Q00102Q0017007400142Q0099011600103Q0030950116006F00704Q001600103Q00302Q0016007100724Q001600103Q00122Q001700073Q00202Q00170017000800122Q0018006E3Q00122Q0019006E3Q00122Q001A006E6Q0017001A000200102Q0016006D001700122Q001600773Q00202Q0016001600084Q001700136Q00160002000200104Q00770016001269011400073Q00204401140014003200104Q0031001400122Q001400073Q00202Q00140014003200104Q003300142Q0064012Q00017Q000A3Q00030A3Q00446973636F2Q6E65637403073Q0044657374726F79030B3Q0043752Q72656E74526F636B00028Q00030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D6503143Q00204D696E696E67204C2Q6F702053544F2Q50454403053Q007072696E7403303Q005B466F726765204D696E696E675D204D696E696E672053746F2Q706564202D20436C65616E757020436F6D706C65746500324Q0099016Q000608012Q000800013Q00044F3Q000800012Q0099016Q002018014Q00012Q007B012Q000200012Q001A017Q0097017Q0099012Q00013Q000608012Q001000013Q00044F3Q001000012Q0099012Q00013Q002018014Q00012Q007B012Q000200012Q001A017Q0097012Q00014Q0099012Q00024Q00F23Q000100016Q00038Q000100016Q00048Q000100016Q00053Q00064Q001E00013Q00044F3Q001E00012Q0099012Q00053Q002018014Q00022Q007B012Q000200012Q001A017Q0097012Q00054Q0099012Q00064Q00543Q000100016Q00078Q000100016Q00083Q00304Q0003000400124Q00058Q00098Q00083Q00304Q000600046Q00083Q00304Q000700056Q000A3Q00122Q000100086Q000200018Q0002000100124Q00093Q00122Q0001000A8Q000200016Q00017Q00213Q0003103Q0053652Q73696F6E537461727454696D6503043Q007469636B030A3Q00546F74616C4D696E6564028Q0003133Q004C6173744D61696E74656E616E636554696D6503103Q004D61696E74656E616E6365436F756E74030C3Q0043752Q72656E745068617365030A3Q00536B69704672616D6573030E3Q00536B69704D696E654672616D657303113Q004C6173744F7265536B69704E6F74696679030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B7303123Q0043616D6572615368616B65526573746F72650003123Q004C6173745072696F7269747953776974636803113Q005072696F726974794C6F636B556E74696C03143Q004C6173745072696F72697479526F636B5479706503153Q005072696F7269747954797065432Q6F6C646F776E7303113Q004C6173745072696F72697479436865636B030F3Q004C617374526F636B52656672657368030D3Q0050656E64696E67537769746368010003113Q004C61737450656E64696E67537769746368030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D6503183Q00204D696E696E67204C2Q6F70205354415254494E473Q2E03053Q007072696E7403213Q005B466F726765204D696E696E675D205374617274696E67204D696E696E673Q2E03093Q0048656172746265617403073Q00436F2Q6E65637403043Q007461736B03053Q00737061776E031D3Q005B466F726765204D696E696E675D204D696E696E67205374617274656400824Q0099017Q00992Q0100014Q00313Q00020002000608012Q000600013Q00044F3Q000600012Q0064012Q00014Q0099012Q00013Q000608012Q000B00013Q00044F3Q000B00012Q001A017Q0097012Q00014Q0099012Q00023Q00126B2Q0100026Q00010001000200104Q000100016Q00023Q00304Q000300046Q00023Q00122Q000100026Q00010001000200104Q000500016Q00023Q00304Q000600046Q00023Q00304Q000700046Q00023Q00304Q000800046Q00023Q00304Q000900046Q00023Q00304Q000A00046Q00026Q00015Q00104Q000B00016Q00026Q00015Q00104Q000C00016Q00023Q00304Q000D000E6Q00023Q00304Q000F00046Q00023Q00304Q001000046Q00023Q00304Q0011000E6Q00026Q00015Q00104Q001200016Q00023Q00304Q001300046Q00023Q00122Q000100026Q00010001000200104Q001400016Q00023Q00304Q001500166Q00023Q00304Q001700046Q00023Q00304Q0018000E6Q00023Q00122Q000100026Q00010001000200104Q001900016Q00033Q00122Q0001001A6Q000200018Q0002000100124Q001B3Q00122Q0001001C8Q000200016Q00048Q000100016Q00058Q000100016Q00068Q000100016Q00078Q000100016Q00093Q00206Q001D00206Q001E00068201023Q000100052Q0099012Q000A4Q0099012Q000B4Q0099012Q000C4Q0099012Q000D4Q0099012Q000E4Q00443Q000200022Q0097012Q00083Q001269012Q001F3Q00204D014Q00200006822Q010001000100022Q0099012Q000A4Q0099012Q000F4Q007B012Q000200012Q0099012Q00093Q00204D014Q001D002018014Q001E00068201020002000100182Q0099012Q000A4Q0099012Q00104Q0099012Q00024Q0099012Q00114Q0099012Q00124Q0099012Q00034Q0099012Q000B4Q0099012Q00134Q0099012Q00144Q0099012Q00154Q0099012Q00164Q0099012Q00174Q0099012Q00184Q0099012Q00194Q0099012Q001A4Q0099012Q001B4Q0099012Q001C4Q0099012Q001D4Q0099012Q001E4Q0099012Q001F4Q0099012Q00204Q0099012Q00214Q0099012Q00224Q0099012Q00234Q0040012Q000200026Q00013Q00124Q001B3Q00122Q000100218Q000200016Q00013Q00033Q000C3Q00030A3Q004175746F4D696E696E67030A3Q00446973636F2Q6E65637403053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q0042617365506172742Q01030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637403063Q00506172656E74030A3Q0043616E436F2Q6C696465012Q003A4Q0099016Q00204D014Q000100060D012Q00050001000100044F3Q000500012Q0064012Q00014Q0099012Q00014Q00033Q0001000200060D012Q000A0001000100044F3Q000A00012Q0064012Q00014Q00992Q0100023Q0006A73Q002C0001000100044F3Q002C00012Q006D2Q016Q00972Q0100034Q0097012Q00024Q00992Q0100043Q0006082Q01001800013Q00044F3Q001800012Q00992Q0100043Q0020182Q01000100022Q007B2Q01000200012Q001A2Q0100014Q00972Q0100043Q0012692Q0100033Q00201801023Q00042Q0041000200034Q00222Q013Q000300044F3Q00240001002018010600050005001243000800064Q00440006000800020006080106002400013Q00044F3Q002400012Q0099010600033Q0020120006000500070006AA0001001D0001000200044F3Q001D000100204D2Q013Q00080020182Q010001000900068201033Q000100012Q0099012Q00034Q00440001000300022Q00972Q0100043Q0012692Q0100034Q0099010200034Q001C00010002000300044F3Q0037000100204D01050004000A0006080105003700013Q00044F3Q0037000100204D01050004000B0006080105003700013Q00044F3Q0037000100306D0004000B000C0006AA000100300001000100044F3Q003000012Q0064012Q00013Q00013Q00053Q002Q033Q0049734103083Q0042617365506172742Q01030A3Q0043616E436F2Q6C696465010001093Q0020182Q013Q0001001243000300024Q00440001000300020006082Q01000800013Q00044F3Q000800012Q00992Q015Q00201200013Q000300306D3Q000400052Q0064012Q00017Q00043Q00030A3Q004175746F4D696E696E6703043Q007461736B03043Q0077616974026Q00E03F00104Q0099016Q00204D014Q0001000608012Q000F00013Q00044F3Q000F0001001269012Q00023Q00204D014Q0003001243000100044Q007B012Q000200012Q0099016Q00204D014Q0001000608014Q00013Q00044F5Q00012Q0099012Q00014Q00A43Q0001000100044F5Q00012Q0064012Q00017Q005C3Q00030A3Q004175746F4D696E696E6703043Q007469636B030D3Q004C617374536B69705265736574026Q004E40028Q0003063Q00737472696E6703063Q00666F726D6174032D3Q0020506572696F64696320636C65616E7570207C20536B692Q7065643A2564204F72654E6F7469666965643A2564030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030C3Q0043752Q72656E745068617365030B3Q0043752Q72656E74526F636B00030A3Q00536B69704672616D6573026Q000840032D3Q002043686172616374657220646965642F7265737061776E696E67202D20506861736520726573657420746F203003253Q0020526F636B2048503D30207C20537769746368696E6720692Q6D6564696174656C793Q2E030A3Q00546F74616C4D696E6564026Q00F03F030C3Q00536B692Q706564526F636B73026Q00144003073Q00556E6B6E6F776E030D3Q004C6F636B65644D696E65506F7303133Q0020492Q6D656469617465205377697463683A2003023Q002Q20030E3Q00536B69704D696E654672616D657303123Q004C6173745072696F7269747953776974636803143Q004C6173745072696F72697479526F636B5479706503083Q00746F6E756D62657203113Q005072696F726974794477652Q6C54696D6503113Q005072696F726974794C6F636B556E74696C03203Q00204E6F20726F636B20666F756E642061667465722048503D3020737769746368030D3Q0050656E64696E6753776974636803113Q004C61737450656E64696E67537769746368029A5Q99C93F0100030C3Q004D617463686564526F636B7303143Q005072696F72697479536B6970432Q6F6C646F776E031E3Q0020416C72656164792D6D696E696E67207377697463683A2025732Q202573026Q002440032A3Q00204E6F20726F636B20666F756E6420616674657220616C72656164792D6D696E696E672073776974636803143Q005072696F726974795363616E496E74657276616C03163Q005072696F72697479537769746368432Q6F6C646F776E03113Q004C6173745072696F72697479436865636B030F3Q005072696F72697479456E61626C6564026Q001040030F3Q004F7265536B69704E6F746966696564030E3Q00526F636B5072696F72697469657303223Q00205052494F52495459205357495443483A20257328502564292Q202573285025642903043Q006D6174682Q033Q006D6178026Q002040030E3Q004C617374526F636B536561726368030D3Q004E6F54617267657453696E636503143Q00412Q6C6F774F726546696C746572427970612Q7303153Q0049676E6F72654F726546696C74657273556E74696C026Q00184003323Q00204E6F2074617267657420666F756E642C2074656D706F726172696C792069676E6F72696E67206F72652066696C74657273030D3Q004C6173744E6F526F636B4C6F67030D3Q0053656C656374656441726561732Q033Q00412Q6C03053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C03413Q00204E4F20524F434B20464F554E44207C2041726561733A202573207C20537061776E733A202564207C20536B692Q7065643A202564207C2052616E67653A20256403083Q00746F737472696E67030B3Q004D696E696E6752616E6765030D3Q0020526F636B204D696E65643A20026Q002E40030D3Q00204E657720526F636B3A202573030B3Q002053776974636865643A2003013Q003F030E3Q004C6173744C2Q6F6B54617267657403083Q00506F736974696F6E030E3Q005361666548656967687449646C6503013Q0059030A3Q0047686F737453702Q6564026Q00E03F03063Q00434672616D652Q033Q006E657703013Q00582Q033Q006D696E03013Q005A03083Q00526F746174696F6E03163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q00506C6174666F726D5374616E643Q017F033Q00992Q015Q00204D2Q010001000100060D2Q0100050001000100044F3Q000500012Q0064012Q00014Q00992Q0100014Q009A00010001000100122Q000100026Q0001000100024Q000200023Q00202Q0002000200034Q000100010002000E2Q000400230001000100044F3Q002300012Q00992Q0100034Q00030001000100022Q0099010200044Q0003000200010002000E12010500160001000100044F3Q00160001000ED50005001F0001000200044F3Q001F00012Q0099010300053Q001237010400063Q00202Q00040004000700122Q000500086Q000600016Q000700026Q0004000700024Q000500016Q0003000500012Q0099010300023Q001269010400024Q00030004000100020010E10003000300042Q00992Q0100064Q00042Q01000100024Q000200076Q000300016Q00020002000200062Q0003002D0001000100044F3Q002D00010020180103000100090012430005000A4Q00440003000500020006080102003100013Q00044F3Q0031000100060D010300410001000100044F3Q004100012Q0099010400023Q00204D01040004000B0026E5000400400001000500044F3Q004000012Q0099010400023Q00300A0004000B00054Q000400023Q00302Q0004000C000D4Q000400023Q00302Q0004000E000F4Q000400086Q0004000100014Q000400053Q00122Q000500106Q0004000200012Q0064012Q00014Q0099010400023Q00204D01040004000C000608010400AE00013Q00044F3Q00AE00012Q0099010400094Q0099010500023Q00204D01050005000C2Q00310004000200020026E5000400AE0001000D00044F3Q00AE00010026E7000400AE0001000500044F3Q00AE00012Q0099010500053Q001243000600114Q008B010700014Q00260105000700012Q0099010500024Q0099010600023Q00204D01060006001200207D0006000600130010E10005001200062Q0099010500023Q00204D0105000500142Q0099010600023Q00204D01060006000C001269010700024Q000300070001000200207D0007000700152Q007B0005000600072Q00EB0005000A6Q000600023Q00202Q00060006000C4Q00050002000200062Q000500650001000100044F3Q00650001001243000500164Q0099010600023Q00204D01060006000C2Q0099010700023Q00306D0007000C000D2Q0099010700023Q00306D0007000B00052Q0099010700023Q00306D00070017000D2Q0099010700024Q00990108000B4Q00030008000100020010E10007000C00082Q00990107000C4Q0090010800064Q007B0107000200012Q00990107000D4Q0099010800023Q00204D01080008000C2Q007B0107000200012Q0099010700023Q00204D01070007000C000608010700AB00013Q00044F3Q00AB00012Q00990107000A4Q0099010800023Q00204D01080008000C2Q003100070002000200060D010700830001000100044F3Q00830001001243000700164Q0099010800053Q001271010900186Q000A00053Q00122Q000B00196Q000C00076Q00090009000C4Q000A00016Q0008000A000100122Q000800056Q0008000E6Q000800023Q00302Q0008001A00154Q000800023Q00122Q000900026Q00090001000200102Q0008001B00094Q000800023Q00102Q0008001C000700122Q0008001D6Q00095Q00202Q00090009001E4Q00080002000200062Q000800A30001000100044F3Q00A300012Q00990108000F3Q000608010800A200013Q00044F3Q00A200012Q00990108000F3Q00204D01080008001E00060D010800A30001000100044F3Q00A30001001243000800053Q000ED5000500AE0001000800044F3Q00AE00012Q0099010900023Q001271000A00026Q000A000100024Q000A000A000800102Q0009001F000A00044Q00AE00012Q0099010700053Q001243000800204Q007B010700020001001269010400024Q00030004000100022Q0099010500023Q00204D010500050021000608010500142Q013Q00044F3Q00142Q012Q0099010500023Q00204D0105000500222Q0079010500040005000E80002300142Q01000500044F3Q00142Q012Q0099010500023Q0010BF0005002200044Q000500023Q00302Q0005002100244Q000500023Q00202Q00050005000C00062Q000500142Q013Q00044F3Q00142Q012Q0099010500023Q0020D80005000500254Q000600023Q00202Q00060006000C4Q00050005000600062Q000500142Q01000100044F3Q00142Q012Q00990105000A4Q0099010600023Q00204D01060006000C2Q003100050002000200060D010500CF0001000100044F3Q00CF0001001243000500163Q0012690106001D4Q009901075Q00204D0107000700262Q003100060002000200060D010600DD0001000100044F3Q00DD00012Q00990106000F3Q000608010600DC00013Q00044F3Q00DC00012Q00990106000F3Q00204D01060006002600060D010600DD0001000100044F3Q00DD0001001243000600054Q0099010700023Q00304D0007000C000D4Q000700023Q00302Q0007000B00054Q000700023Q00302Q00070017000D4Q000700026Q0008000B6Q00080001000200102Q0007000C00084Q0007000D6Q000800023Q00202Q00080008000C4Q0007000200014Q000700023Q00202Q00070007000C00062Q000700102Q013Q00044F3Q00102Q012Q00990107000A4Q0099010800023Q00204D01080008000C2Q003100070002000200060D010700F60001000100044F3Q00F60001001243000700163Q000ED5000500FE0001000600044F3Q00FE0001000608010500FE00013Q00044F3Q00FE00012Q0099010800104Q0090010900054Q0090010A00064Q00260108000A00012Q0099010800053Q0012DE000900063Q00202Q00090009000700122Q000A00276Q000B00056Q000C00076Q0009000C00024Q000A00016Q0008000A000100122Q000800056Q0008000E6Q000800023Q00302Q0008000E000F4Q000800023Q00302Q0008001A00284Q000800023Q00102Q0008001C000700044Q00142Q012Q0099010700053Q001243000800294Q008B010900014Q00260107000900010012690105001D4Q009901065Q00204D01060006002A2Q003100050002000200060D010500222Q01000100044F3Q00222Q012Q00990105000F3Q000608010500212Q013Q00044F3Q00212Q012Q00990105000F3Q00204D01050005002A00060D010500222Q01000100044F3Q00222Q01001243000500233Q0012690106001D4Q009901075Q00204D01070007002B2Q003100060002000200060D010600302Q01000100044F3Q00302Q012Q00990106000F3Q0006080106002F2Q013Q00044F3Q002F2Q012Q00990106000F3Q00204D01060006002B00060D010600302Q01000100044F3Q00302Q01001243000600053Q0012690107001D4Q009901085Q00204D01080008001E2Q003100070002000200060D0107003E2Q01000100044F3Q003E2Q012Q00990107000F3Q0006080107003D2Q013Q00044F3Q003D2Q012Q00990107000F3Q00204D01070007001E00060D0107003E2Q01000100044F3Q003E2Q01001243000700054Q0099010800023Q00204D01080008002C2Q007901080004000800065C010500020001000800044F3Q00442Q012Q00EF00086Q008B010800013Q00263F0106004D2Q01000500044F3Q004D2Q012Q0099010900023Q00204D01090009001B2Q007901090004000900065C010600020001000900044F3Q004D2Q012Q00EF00096Q008B010900014Q0099010A00023Q00204D010A000A001A00263F010A00532Q01000500044F3Q00532Q012Q00EF000A6Q008B010A00014Q0099010B00023Q00204D010B000B001F00060D010B00592Q01000100044F3Q00592Q01001243000B00053Q00065C010B00020001000400044F3Q005C2Q012Q00EF000B6Q008B010B00014Q0099010C00023Q00204D010C000C000C000608010C00662Q013Q00044F3Q00662Q012Q0099010C00023Q00204D010C000C00252Q0099010D00023Q00204D010D000D000C2Q00C0000C000C000D2Q0099010D00023Q00204D010D000D000C000608010D00F42Q013Q00044F3Q00F42Q012Q0099010D5Q00204D010D000D002D000608010D00F42Q013Q00044F3Q00F42Q0100060D010C00F42Q01000100044F3Q00F42Q01000608010800F42Q013Q00044F3Q00F42Q01000608010900F42Q013Q00044F3Q00F42Q01000608010A00F42Q013Q00044F3Q00F42Q01000608010B00F42Q013Q00044F3Q00F42Q012Q0099010D00023Q0010E1000D002C00042Q0099010D00023Q00204D010D000D000B0026DF000D00862Q01002E00044F3Q00862Q012Q0099010D00023Q0020D8000D000D002F4Q000E00023Q00202Q000E000E000C4Q000D000D000E00062Q000D00862Q01000100044F3Q00862Q0100044F3Q00F42Q012Q0099010D00114Q0099010E00023Q00204D010E000E000C2Q0031000D00020002000608010D00F42Q013Q00044F3Q00F42Q012Q0099010E00023Q002002000E000E000C4Q000F000A6Q0010000E6Q000F0002000200062Q000F00942Q01000100044F3Q00942Q01001243000F00164Q009901105Q00204D0110001000302Q00C000100010000F00060D0110009A2Q01000100044F3Q009A2Q01001243001000054Q00990111000A4Q00900112000D4Q003100110002000200060D011100A02Q01000100044F3Q00A02Q01001243001100164Q009901125Q00204D0112001200302Q00C000120012001100060D011200A62Q01000100044F3Q00A62Q01001243001200054Q0099011300053Q001269011400063Q00204D011400140007001243001500314Q00900116000F4Q0090011700104Q0090011800114Q0090011900124Q00440014001900022Q008B011500014Q00260113001500010012690113001D4Q009901145Q00204D0114001400262Q003100130002000200060D011300BF2Q01000100044F3Q00BF2Q012Q00990113000F3Q000608011300BE2Q013Q00044F3Q00BE2Q012Q00990113000F3Q00204D01130013002600060D011300BF2Q01000100044F3Q00BF2Q01001243001300053Q000ED5000500C92Q01001300044F3Q00C92Q01000608010E00C92Q013Q00044F3Q00C92Q012Q0099011400023Q00204D011400140014001269011500024Q00030015000100022Q00620015001500132Q007B0014000E0015000ED5000500D12Q01001300044F3Q00D12Q01000608010F00D12Q013Q00044F3Q00D12Q012Q0099011400104Q00900115000F4Q0090011600134Q00260114001600012Q00990114000C4Q002D0015000E6Q0014000200014Q001400023Q00102Q0014000C000D4Q001400023Q00302Q0014000B00054Q001400023Q00302Q00140017000D4Q0014000D6Q001500023Q00204D01150015000C2Q005D00140002000100122Q001400056Q0014000E6Q001400023Q00122Q001500323Q00202Q0015001500334Q001600023Q00202Q00160016001A00062Q001600E82Q01000100044F3Q00E82Q01001243001600053Q001243001700344Q00440015001700020010E10014001A00152Q0099011400023Q0010E10014001B00042Q0099011400023Q0010E10014001C0011000ED5000500F42Q01000700044F3Q00F42Q012Q0099011400024Q00620015000400070010E10014001F00152Q0099010D00023Q00204D010D000D000C000608010D00FF2Q013Q00044F3Q00FF2Q012Q0099010D00124Q0099010E00023Q00204D010E000E000C2Q008B010F00014Q0044000D000F000200060D010D00300301000100044F3Q003003012Q008B010D00014Q0099010E00023Q00204D010E000E000C00060D010E00100201000100044F3Q001002012Q0099010E00023Q00204D010E000E0035000608010E001002013Q00044F3Q00100201001269010E00024Q00E4000E000100024Q000F00023Q00202Q000F000F00354Q000E000E000F00262Q000E00100201002300044F3Q001002012Q008B010D5Q000608010D003003013Q00044F3Q003003012Q0099010E00023Q001269010F00024Q0003000F000100020010E1000E0035000F2Q0099010E00023Q00204D010E000E000C2Q0099010F00024Q00990110000B4Q00030010000100020010E1000F000C00102Q0099010F000D4Q0099011000023Q00204D01100010000C2Q007B010F000200012Q0099010F00023Q00204D010F000F000C000608010F002702013Q00044F3Q002702012Q0099010F00023Q00306D000F0036000D00044F3Q005102012Q0099010F00023Q00204D010F000F003600060D010F00300201000100044F3Q003002012Q0099010F00023Q001269011000024Q00030010000100020010E1000F0036001000044F3Q00510201001269010F00024Q006A000F000100024Q001000023Q00202Q0010001000364Q000F000F0010000E2Q000F00510201000F00044F3Q005102012Q0099010F5Q00204D010F000F0037000608010F004F02013Q00044F3Q004F02012Q0099010F00023Q00204D010F000F0038000608010F004502013Q00044F3Q00450201001269010F00024Q0003000F000100022Q0099011000023Q00204D0110001000380006F4001000510201000F00044F3Q005102012Q0099010F00023Q001269001000026Q00100001000200202Q00100010003900102Q000F003800104Q000F00053Q00122Q0010003A6Q001100016Q000F0011000100044Q005102012Q0099010F00023Q00306D000F003800052Q0099010F00023Q00204D010F000F000C00060D010F00B60201000100044F3Q00B602012Q0099010F00023Q00204D010F000F003B000608010F006002013Q00044F3Q00600201001269010F00024Q006A000F000100024Q001000023Q00202Q00100010003B4Q000F000F0010000E2Q001500B60201000F00044F3Q00B602012Q0099010F00134Q0003000F00010002001243001000053Q001243001100054Q009901125Q00204D01120012003C2Q0034001200123Q000ED50005006E0201001200044F3Q006E02012Q009901125Q00204D01120012003C2Q0034001200123Q00060D0112006F0201000100044F3Q006F02010012430012003D3Q0012690113003E4Q0099011400023Q00204D0114001400142Q001C00130002001500044F3Q0075020100207D0011001100130006AA001300740201000100044F3Q00740201000608010F00A402013Q00044F3Q00A402012Q009901135Q00204D01130013003C2Q0034001300133Q0026DF001300940201000500044F3Q009402010012690113003E3Q0020180114000F003F2Q0041001400154Q002201133Q001500044F3Q00910201002018011800170040001243001A00414Q00440018001A000200060D0118008D0201000100044F3Q008D0201002018011800170040001243001A00424Q00440018001A00020006080118009102013Q00044F3Q0091020100201801180017003F2Q00310018000200022Q0034001800184Q00620010001000180006AA001300830201000200044F3Q0083020100044F3Q00A402010012690113003E4Q009901145Q00204D01140014003C2Q001C00130002001500044F3Q00A202010020180118000F00092Q0090011A00174Q00440018001A0002000608011800A202013Q00044F3Q00A2020100201801190018003F2Q00310019000200022Q0034001900194Q00620010001000190006AA001300990201000200044F3Q009902012Q0099011300053Q001223011400063Q00202Q00140014000700122Q001500433Q00122Q001600446Q001700126Q0016000200024Q001700106Q001800116Q00195Q00202Q0019001900452Q00440014001900022Q002F001500016Q0013001500014Q001300023Q00122Q001400026Q00140001000200102Q0013003B0014000608010E00D702013Q00044F3Q00D702012Q0099010F00023Q00204D010F000F000C00060D010F00D70201000100044F3Q00D702012Q0099010F00053Q0012C1001000466Q0011000A6Q0012000E6Q00110002000200062Q001100C40201000100044F3Q00C40201001243001100164Q00ED0010001000112Q007B010F000200012Q0099010F00144Q001A011000104Q007B010F000200012Q0099010F00024Q0099011000023Q00204D01100010001200207D0010001000130010E1000F001200102Q0099010F00023Q00306D000F000B00052Q009D000F00023Q00302Q000F000E000F4Q000F00023Q00302Q000F001A00474Q000F00023Q00302Q000F0017000D00044Q0030030100060D010E00FA0201000100044F3Q00FA02012Q0099010F00023Q00204D010F000F000C000608010F00FA02013Q00044F3Q00FA02012Q0099010F00053Q001269011000063Q00204D011000100007001243001100484Q00EB0012000A6Q001300023Q00202Q00130013000C4Q00120002000200062Q001200E80201000100044F3Q00E80201001243001200164Q00CB001000124Q00B6000F3Q00012Q0099010F00144Q00990110000A4Q0099011100023Q00204D01110011000C2Q0041001000114Q00B6000F3Q0001001243000F00054Q0097010F000E4Q0099010F00023Q00306D000F000B00052Q0099010F00023Q00306D000F000E000F2Q0099010F00023Q00306D000F001A00472Q0064012Q00013Q00044F3Q00300301000608010E003003013Q00044F3Q003003012Q0099010F00023Q00204D010F000F000C000608010F003003013Q00044F3Q003003012Q0099010F00023Q00204D010F000F000C0006A7000E00300301000F00044F3Q003003012Q0099010F00053Q0012C1001000496Q0011000A6Q0012000E6Q00110002000200062Q0011000C0301000100044F3Q000C03010012430011004A3Q001243001200194Q00EB0013000A6Q001400023Q00202Q00140014000C4Q00130002000200062Q001300140301000100044F3Q001403010012430013004A4Q00ED0010001000132Q0029010F000200014Q000F00146Q0010000A6Q001100023Q00202Q00110011000C4Q001000116Q000F3Q000100122Q000F00056Q000F000E6Q000F00023Q00302Q000F000B00054Q000F00023Q00302Q000F000E000F4Q000F00023Q00302Q000F001A00474Q000F00023Q00302Q000F0017000D4Q000F00156Q001000023Q00202Q00100010000C4Q000F0002000200062Q000F002F03013Q00044F3Q002F03012Q0099011000023Q00204D0111000F004C0010E10010004B00112Q0064012Q00014Q0099010D00164Q0094010E00046Q000D000200014Q000D00023Q00202Q000D000D000C00062Q000D005F0301000100044F3Q005F03012Q0099010D5Q002061000D000D004D00202Q000E0002004C00202Q000F000E004E00202Q0010000D001500062Q000F00520301001000044F3Q005203012Q0099010F5Q0020CF000F000F004F4Q000F000F3Q00202Q000F000F005000202Q0010000E004E4Q00100010000F00122Q001100513Q00202Q00110011005200202Q0012000E005300122Q001300323Q00202Q0013001300542Q0090011400104Q004E0015000D6Q00130015000200202Q0014000E00554Q00110014000200202Q00120002005100202Q0012001200564Q00110011001200102Q000200510011001269010F00583Q002009010F000F005900102Q00020057000F00122Q000F00583Q00202Q000F000F005900102Q0002005A000F00202Q000F0003005B00062Q000F005C0301000100044F3Q005C030100306D0003005B005C2Q0099010F00023Q00306D000F000B00052Q0064012Q00014Q0099010D00023Q00204D010D000D000E000ED50005006F0301000D00044F3Q006F03012Q0099010D00024Q0049000E00023Q00202Q000E000E000E00202Q000E000E001300102Q000D000E000E00122Q000D00583Q00202Q000D000D005900102Q00020057000D00122Q000D00583Q00202Q000D000D005900102Q0002005A000D6Q00014Q0099010D00154Q0099010E00023Q00204D010E000E000C2Q0031000D0002000200060D010D00780301000100044F3Q007803012Q0099010E00023Q00306D000E000C000D2Q0064012Q00014Q0099010E00174Q0090010F00024Q0090011000034Q00900111000D4Q009001126Q0026010E001200012Q0064012Q00017Q00103Q0003023Q005F4703053Q00466F726765030A3Q004661726D436F6E66696703083Q004175746F4661726D03083Q0053746F704661726D0100030E3Q004661726D5549456C656D656E7473030E3Q004175746F4661726D546F2Q676C6503053Q007063612Q6C03053Q005469746C65030B3Q004175746F204D696E696E6703073Q00436F6E74656E7403253Q004175746F204661726D2064697361626C656420746F2061766F696420636F6E666C6963747303083Q004475726174696F6E027Q0040030A3Q004175746F4D696E696E6701343Q000608012Q002600013Q00044F3Q002600010012692Q0100013Q00204D2Q01000100020006B8000200070001000100044F3Q0007000100204D0102000100030006080102002600013Q00044F3Q0026000100204D0103000200040006080103002600013Q00044F3Q0026000100204D0103000100050006080103001200013Q00044F3Q0012000100204D0103000100052Q00A400030001000100044F3Q0020000100306D0002000400060006B8000300160001000100044F3Q0016000100204D0103000100070006080103001F00013Q00044F3Q001F000100204D0104000300080006080104001F00013Q00044F3Q001F0001001269010400093Q00068201053Q000100012Q0090012Q00034Q007B0104000200012Q005800036Q009901036Q001D00043Q000300302Q0004000A000B00302Q0004000C000D00302Q0004000E000F4Q0003000200012Q00992Q0100013Q0010E1000100103Q000608012Q002F00013Q00044F3Q002F00012Q00992Q0100024Q00A40001000100012Q00992Q0100034Q00A400010001000100044F3Q003300012Q00992Q0100044Q00A40001000100012Q00992Q0100054Q00A40001000100012Q0064012Q00013Q00013Q00023Q00030E3Q004175746F4661726D546F2Q676C652Q033Q0053657400064Q0019016Q00206Q000100206Q00024Q00029Q00000200016Q00019Q002Q0001044Q00992Q016Q009001026Q007B2Q01000200012Q0064012Q00017Q00023Q00030E3Q00537475636B446574656374696F6E03073Q00456E61626C656401044Q00992Q015Q00204D2Q01000100010010E1000100024Q0064012Q00017Q00023Q00030E3Q00537475636B446574656374696F6E03153Q00506F736974696F6E436865636B496E74657276616C01044Q00992Q015Q00204D2Q01000100010010E1000100024Q0064012Q00017Q00023Q00030E3Q00537475636B446574656374696F6E03113Q00506F736974696F6E5468726573686F6C6401044Q00992Q015Q00204D2Q01000100010010E1000100024Q0064012Q00017Q00073Q0003053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403163Q004D61696E74656E616E636520706572666F726D65642103083Q004475726174696F6E027Q0040000B3Q001269012Q00013Q0006822Q013Q000100012Q0099017Q007B012Q000200012Q0099012Q00014Q00322Q013Q000300302Q00010002000300302Q00010004000500302Q0001000600076Q000200016Q00013Q00018Q00034Q0099017Q00A43Q000100012Q0064012Q00017Q00103Q0003103Q0053652Q73696F6E537461727454696D65028Q0003043Q007469636B03083Q002Q303A2Q303A2Q3003063Q006763696E666F026Q004E40030A3Q00546F74616C4D696E656403053Q005469746C65030C3Q004D696E696E6720537461747303073Q00436F6E74656E7403063Q00737472696E6703063Q00666F726D6174033E3Q00557074696D653A2025730A4D696E65643A2025640A4D504D3A20252E31660A4D61696E74656E616E63653A2025640A4D656D6F72793A20252E3166204B4203103Q004D61696E74656E616E6365436F756E7403083Q004475726174696F6E026Q00144000374Q0099016Q00204D014Q0001000ED50002000D00013Q00044F3Q000D00012Q0099012Q00013Q0012692Q0100034Q00030001000100022Q009901025Q00204D0102000200012Q00792Q01000100022Q00313Q0002000200060D012Q000E0001000100044F3Q000E00010012433Q00043Q0012692Q0100054Q00030001000100022Q009901025Q00204D010200020001000ED50002001C0001000200044F3Q001C0001001269010200034Q009C0102000100024Q00035Q00202Q0003000300014Q00020002000300202Q00020002000600062Q0002001D0001000100044F3Q001D0001001243000200023Q000ED5000200240001000200044F3Q002400012Q009901035Q00204D0103000300072Q00A001030003000200060D010300250001000100044F3Q00250001001243000300024Q0099010400024Q001E00053Q000300302Q00050008000900122Q0006000B3Q00202Q00060006000C00122Q0007000D6Q00088Q00095Q00202Q0009000900074Q000A00036Q000B5Q00202Q000B000B000E4Q000C00016Q0006000C000200102Q0005000A000600302Q0005000F00104Q0004000200016Q00017Q00073Q00030D3Q0053656C65637465644172656173028Q0003053Q0070616972732Q0103053Q007461626C6503063Q00696E7365727403043Q00736F727401364Q00992Q015Q0006082Q01000500013Q00044F3Q000500012Q006D2Q016Q00972Q0100014Q00992Q0100023Q00204D2Q01000100012Q0034000100013Q0026DF000100110001000200044F3Q001100012Q00992Q0100033Q0006330102000E00013Q00044F3Q000E00012Q009901026Q00310001000200022Q00972Q0100013Q00044F3Q003300012Q006D2Q015Q001239010200036Q000300023Q00202Q0003000300014Q00020002000400044Q00200001001269010700034Q009A010800046Q000900066Q000800096Q00073Q000900044Q001E00010020120001000B00040006AA0007001D0001000200044F3Q001D00010006AA000200170001000200044F3Q001700012Q006D01026Q0061010200013Q00122Q000200036Q000300016Q00020002000400044Q002D0001001269010600053Q00204D0106000600062Q0099010700014Q0090010800054Q00260106000800010006AA000200280001000100044F3Q00280001001269010200053Q00204D0102000200072Q0099010300014Q007B0102000200012Q008B2Q016Q00972Q016Q0064012Q00017Q000C3Q00030E3Q0046696C746572536C6F74314F7265030E3Q0046696C746572536C6F74324F7265030E3Q0046696C746572536C6F74334F726503063Q00286E6F6E652903063Q0069706169727303053Q007461626C6503063Q00696E73657274030D3Q0043752Q72656E744F7074696F6E03043Q007479706503053Q007063612Q6C03133Q002853656C656374206172656120666972737429028Q00015D4Q002A000100016Q00028Q0001000200024Q00018Q000100036Q000200023Q00202Q0002000200014Q000300023Q00202Q0003000300024Q000400023Q00204D0104000400032Q00050001000300012Q006D010200013Q001243000300044Q0005000200010001001269010300054Q009901046Q001C00030002000500044F3Q00180001001269010800063Q00204D0108000800072Q0090010900024Q0090010A00074Q00260108000A00010006AA000300130001000200044F3Q001300010002B300035Q001269010400054Q0090010500014Q001C00040002000600044F3Q005A00010006080108005900013Q00044F3Q0059000100204D010900080008001269010A00094Q0090010B00094Q0031000A000200020026DF000A00290001000600044F3Q00290001000633010A00310001000900044F3Q003100010006080109003000013Q00044F3Q003000012Q006D010A00014Q0090010B00094Q0005000A0001000100060D010A00310001000100044F3Q003100012Q006D010A5Q001269010B000A3Q000682010C0001000100022Q0090012Q00084Q0090012Q00024Q0028000B000200014Q000B5Q00122Q000C00056Q000D000A6Q000C0002000E00044Q004A00010006080110004A00013Q00044F3Q004A00010026E50010004A0001000B00044F3Q004A00012Q0090011100034Q0090011200024Q0090011300104Q00440011001300020006080111004A00013Q00044F3Q004A0001001269011100063Q00204D0111001100072Q00900112000B4Q0090011300104Q00260111001300010006AA000C003B0001000200044F3Q003B00012Q0034000C000B3Q0026DF000C00530001000C00044F3Q005300012Q006D010C00013Q001243000D00044Q0005000C000100012Q0090010B000C3Q001269010C000A3Q000682010D0002000100022Q0090012Q00084Q0090012Q000B4Q007B010C000200012Q005800096Q005800075Q0006AA0004001F0001000200044F3Q001F00012Q0064012Q00013Q00033Q00013Q0003063Q00697061697273020D3Q001269010200014Q009001036Q001C00020002000400044F3Q00080001000618000600080001000100044F3Q000800012Q008B010700014Q00E2000700023Q0006AA000200040001000200044F3Q000400012Q008B01026Q00E2000200024Q0064012Q00017Q00013Q0003073Q005265667265736800054Q0080016Q00206Q00014Q000200018Q000200016Q00017Q00013Q002Q033Q0053657400054Q0080016Q00206Q00014Q000200018Q000200016Q00017Q00153Q00030B3Q0043752Q72656E74526F636B0003053Q007461626C6503043Q0066696E64030B3Q005B412Q6C2041726561735D030D3Q0053656C65637465644172656173028Q0003093Q00417265614C6162656C03093Q00412Q6C20417265617303063Q00636F6E63617403023Q002C2003053Q007063612Q6C030D3Q0053656C6563746564526F636B73030E3Q00526F636B5072696F726974696573030C3Q00526F636B44726F70646F776E03043Q007461736B03053Q00737061776E03063Q00737472696E6703063Q00666F726D6174031F3Q0041726561733A202573207C20526F636B7320617661696C61626C653A2025642Q033Q00412Q6C015E4Q00BB00015Q00302Q00010001000200122Q000100033Q00202Q0001000100044Q00025Q00122Q000300056Q00010003000200062Q0001001000013Q00044F3Q001000012Q0099010200014Q005F01035Q00102Q0002000600034Q000200026Q000300016Q00020002000100044Q001F00012Q003400025Q0026DF0002001A0001000700044F3Q001A00012Q0099010200014Q005F01035Q00102Q0002000600034Q000200026Q000300016Q00020002000100044Q001F00012Q0099010200013Q0010E1000200064Q0099010200024Q008B010300014Q007B0102000200012Q0099010200033Q00204D0102000200080006080102003900013Q00044F3Q003900010006082Q01002800013Q00044F3Q00280001001243000200093Q00060D010200330001000100044F3Q003300012Q003400025Q000ED5000700320001000200044F3Q00320001001269010200033Q00204F01020002000A4Q00035Q00122Q0004000B6Q00020004000200062Q000200330001000100044F3Q00330001001243000200093Q0012690103000C3Q00068201043Q000100022Q0099012Q00034Q0090012Q00024Q007B0103000200012Q005800026Q0099010200014Q005900035Q00102Q0002000D00034Q000200016Q00035Q00102Q0002000E00034Q000200033Q00202Q00020002000F00062Q0002004900013Q00044F3Q00490001001269010200103Q00204D01020002001100068201030001000100022Q0099012Q00034Q0099012Q00044Q007B0102000200012Q0099010200053Q001269010300123Q00204D010300030013001243000400143Q0006082Q01005200013Q00044F3Q00520001001243000500153Q00060D010500590001000100044F3Q005900012Q003400055Q000ED5000700580001000500044F3Q005800012Q003400055Q00060D010500590001000100044F3Q00590001001243000500154Q0099010600044Q0034000600064Q00CB000300064Q00B600023Q00012Q0064012Q00013Q00023Q00033Q0003093Q00417265614C6162656C2Q033Q0053657403013Q002000084Q002E7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q00063Q0003053Q007063612Q6C03043Q007461736B03043Q0077616974029A5Q99B93F03093Q00526F636B4C6162656C030D3Q005072696F726974794C6162656C001E3Q001269012Q00013Q0006822Q013Q000100012Q0099017Q0054012Q0002000100124Q00023Q00206Q000300122Q000100048Q0002000100124Q00013Q0006822Q010001000100022Q0099017Q0099012Q00014Q007B012Q000200012Q0099016Q00204D014Q0005000608012Q001500013Q00044F3Q00150001001269012Q00013Q0006822Q010002000100012Q0099017Q007B012Q000200012Q0099016Q00204D014Q0006000608012Q001D00013Q00044F3Q001D0001001269012Q00013Q0006822Q010003000100012Q0099017Q007B012Q000200012Q0064012Q00013Q00043Q00023Q00030C3Q00526F636B44726F70646F776E2Q033Q0053657400064Q00067Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00043Q00030C3Q00526F636B44726F70646F776E03073Q0052656672657368028Q0003123Q00284E6F20726F636B7320696E206172656129000F4Q00C67Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200044F3Q000A00012Q0099010200013Q00060D0102000D0001000100044F3Q000D00012Q006D010200013Q001243000300044Q00050002000100012Q0026012Q000200012Q0064012Q00017Q00033Q0003093Q00526F636B4C6162656C2Q033Q0053657403103Q0020286E6F6E652073656C65637465642900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403203Q002053656C65637420322B20726F636B7320746F20736574207072696F7269747900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q000B3Q0003053Q004172656173026Q00F03F030C3Q004172656144726F70646F776E03053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403063Q00466F756E642003073Q002061726561732103083Q004475726174696F6E027Q004000204Q00847Q00122Q000100013Q00122Q000200028Q0002000200064Q000700013Q00044F3Q000700012Q0064012Q00014Q0099012Q00024Q008F000100018Q000200026Q00018Q00033Q00206Q000300064Q001400013Q00044F3Q00140001001269012Q00043Q0006822Q013Q000100022Q0099012Q00034Q0099012Q00014Q007B012Q000200012Q0099012Q00044Q003B2Q013Q000300302Q00010005000600122Q000200086Q000300016Q000300033Q00122Q000400096Q00020002000400102Q00010007000200302Q0001000A000B6Q000200012Q0064012Q00013Q00013Q00023Q00030C3Q004172656144726F70646F776E03073Q005265667265736800064Q00787Q00206Q000100206Q00024Q000200018Q000200016Q00017Q001E3Q00030D3Q0053656C65637465644172656173030C3Q004172656144726F70646F776E03053Q007063612Q6C030D3Q0053656C6563746564526F636B73030E3Q00526F636B5072696F726974696573030C3Q00526F636B44726F70646F776E030C3Q0053656C65637465644F726573030E3Q00526F636B4F726546696C7465727303043Q00526F636B0003043Q004F726573030B3Q004F726544726F70646F776E026Q00F03F026Q000840030A3Q0046696C746572536C6F742Q033Q004F726503103Q004C61737446696C746572536F75726365030E3Q004C61737446696C746572526F636B030B3Q0043752Q72656E74526F636B03093Q00417265614C6162656C03093Q00526F636B4C6162656C03083Q004F72654C6162656C030D3Q005072696F726974794C6162656C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403173Q00412Q6C2073656C656374696F6E7320636C65617265642103083Q004475726174696F6E027Q004003383Q0020412Q6C2073656C656374696F6E7320636C6561726564202841726561732C20526F636B732C204F7265732C205072696F72697469657329009D4Q00D19Q0000015Q00104Q000100016Q00013Q00206Q000200064Q000B00013Q00044F3Q000B0001001269012Q00033Q0006822Q013Q000100012Q0099012Q00014Q007B012Q000200012Q0099017Q005900015Q00104Q000400019Q004Q00015Q00104Q000500016Q00013Q00206Q000600064Q001900013Q00044F3Q00190001001269012Q00033Q0006822Q010001000100012Q0099012Q00014Q007B012Q000200012Q0099017Q007500015Q00104Q000700019Q004Q000100036Q00023Q000200302Q00020009000A4Q00035Q00102Q0002000B00034Q00033Q000200302Q00030009000A4Q00045Q00102Q0003000B00044Q00043Q000200302Q00040009000A4Q00055Q00102Q0004000B00054Q0001000300010010E13Q000800012Q0099012Q00013Q00204D014Q000C000608012Q003400013Q00044F3Q00340001001269012Q00033Q0006822Q010002000100012Q0099012Q00014Q007B012Q000200010012433Q000D3Q0012430001000E3Q0012430002000D3Q0004963Q005200012Q0099010400013Q00121B0005000F6Q000600033Q00122Q000700096Q0005000500074Q0004000400054Q000500013Q00122Q0006000F6Q000700033Q00122Q000800106Q0006000600084Q00050005000600062Q0004004A00013Q00044F3Q004A0001001269010600033Q00068201070003000100012Q0090012Q00044Q007B0106000200010006080105005000013Q00044F3Q00500001001269010600033Q00068201070004000100012Q0090012Q00054Q007B0106000200012Q005800045Q0004233Q003800012Q0099012Q00023Q00306D3Q0011000A2Q0099012Q00023Q00306D3Q0012000A2Q002Q012Q00036Q000100018Q000200016Q00013Q00206Q000600064Q006200013Q00044F3Q00620001001269012Q00033Q0006822Q010005000100022Q0099012Q00014Q0099012Q00044Q007B012Q000200012Q0099012Q00054Q008B2Q0100014Q007B012Q000200012Q0099012Q00013Q00204D014Q000C000608012Q006E00013Q00044F3Q006E0001001269012Q00033Q0006822Q010006000100022Q0099012Q00014Q0099012Q00064Q007B012Q000200012Q0099012Q00023Q00306D3Q0013000A2Q0099012Q00013Q00204D014Q0014000608012Q007800013Q00044F3Q00780001001269012Q00033Q0006822Q010007000100012Q0099012Q00014Q007B012Q000200012Q0099012Q00013Q00204D014Q0015000608012Q008000013Q00044F3Q00800001001269012Q00033Q0006822Q010008000100012Q0099012Q00014Q007B012Q000200012Q0099012Q00013Q00204D014Q0016000608012Q008800013Q00044F3Q00880001001269012Q00033Q0006822Q010009000100012Q0099012Q00014Q007B012Q000200012Q0099012Q00013Q00204D014Q0017000608012Q009000013Q00044F3Q00900001001269012Q00033Q0006822Q01000A000100012Q0099012Q00014Q007B012Q000200012Q0099012Q00074Q007F012Q000100016Q00086Q00013Q000300302Q00010018001900302Q0001001A001B00302Q0001001C001D6Q000200016Q00093Q00122Q0001001E6Q000200018Q000200016Q00013Q000B3Q00023Q00030C3Q004172656144726F70646F776E2Q033Q0053657400064Q00067Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030C3Q00526F636B44726F70646F776E2Q033Q0053657400064Q00067Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030B3Q004F726544726F70646F776E2Q033Q0053657400064Q00067Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q00777Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q0026012Q000200012Q0064012Q00017Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q00777Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q0026012Q000200012Q0064012Q00017Q00023Q00030C3Q00526F636B44726F70646F776E03073Q005265667265736800064Q00787Q00206Q000100206Q00024Q000200018Q000200016Q00017Q00043Q00030B3Q004F726544726F70646F776E03073Q0052656672657368028Q00030F3Q00284E6F206F72657320666F756E6429000F4Q00C67Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200044F3Q000A00012Q0099010200013Q00060D0102000D0001000100044F3Q000D00012Q006D010200013Q001243000300044Q00050002000100012Q0026012Q000200012Q0064012Q00017Q00033Q0003093Q00417265614C6162656C2Q033Q00536574030A3Q0020412Q6C20417265617300064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003093Q00526F636B4C6162656C2Q033Q0053657403103Q0020286E6F6E652073656C65637465642900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403273Q00476C6F62616C204F726573202866612Q6C6261636B293A20286E6F6E652073656C65637465642900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403203Q002053656C65637420322B20726F636B7320746F20736574207072696F7269747900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00023Q0003053Q00526F636B73026Q00F03F000B4Q00847Q00122Q000100013Q00122Q000200028Q0002000200064Q000700013Q00044F3Q000700012Q0064012Q00014Q0099012Q00014Q008B2Q016Q007B012Q000200012Q0064012Q00017Q00103Q0003043Q004F726573026Q00F03F03063Q006970616972732Q01030C3Q0053656C65637465644F72657303053Q007461626C6503063Q00696E7365727403193Q004175746F5472696D496E76616C696453656C656374696F6E73030B3Q004F726544726F70646F776E03053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403103Q004F726573207265667265736865643A2003083Q004475726174696F6E027Q004000434Q00847Q00122Q000100013Q00122Q000200028Q0002000200064Q000700013Q00044F3Q000700012Q0064012Q00014Q0099012Q00014Q003E2Q0100018Q000200019Q0000122Q000100036Q000200026Q00010002000300044Q001000010020123Q000500040006AA0001000F0001000200044F3Q000F00012Q006D2Q015Q001239010200036Q000300033Q00202Q0003000300054Q00020002000400044Q002000012Q00C000073Q00060006080107002000013Q00044F3Q00200001001269010700063Q00204D0107000700072Q0090010800014Q0090010900064Q00260107000900010006AA000200180001000200044F3Q001800012Q0099010200033Q00204D0102000200080006080102002E00013Q00044F3Q002E00012Q0034000200014Q0099010300033Q00204D0103000300052Q0034000300033Q0006A70002002E0001000300044F3Q002E00012Q0099010200033Q0010E10002000500012Q0099010200043Q00204D0102000200090006080102003800013Q00044F3Q003800010012690102000A3Q00068201033Q000100032Q0099012Q00044Q0099012Q00024Q0099012Q00034Q007B0102000200012Q0099010200054Q001D01033Q000300302Q0003000B000C00122Q0004000E6Q000500026Q000500056Q00040004000500102Q0003000D000400302Q0003000F00104Q0002000200016Q00013Q00013Q00063Q00030B3Q004F726544726F70646F776E03073Q0052656672657368028Q00030F3Q00284E6F206F72657320666F756E6429030C3Q0053656C65637465644F7265732Q033Q00536574001A4Q00C67Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200044F3Q000A00012Q0099010200013Q00060D0102000D0001000100044F3Q000D00012Q006D010200013Q001243000300044Q00050002000100012Q0026012Q000200012Q0099012Q00023Q00204D014Q00052Q00347Q000ED50003001900013Q00044F3Q001900012Q0099016Q0020395Q000100206Q00064Q000200023Q00202Q0002000200056Q000200012Q0064012Q00017Q00113Q00030D3Q0053656C65637465644172656173028Q002Q033Q00412Q6C03053Q007461626C6503063Q00636F6E63617403023Q002C2003043Q004E6F6E6503093Q00412Q6C20417265617303053Q005469746C6503083Q002041726561733A2003083Q00746F737472696E6703073Q00436F6E74656E7403063Q00737472696E6703063Q00666F726D6174031E3Q002053656C65637465643A2025732Q0A20526F636B7320282564293A0A257303083Q004475726174696F6E026Q00244000434Q0099016Q00204D014Q00012Q00347Q000ED50002000A00013Q00044F3Q000A00012Q0099016Q00204D014Q00012Q00347Q00060D012Q000B0001000100044F3Q000B00010012433Q00034Q00992Q015Q00204D2Q01000100012Q0034000100013Q0026DF000100140001000200044F3Q001400012Q00992Q0100014Q000300010001000200060D2Q0100150001000100044F3Q001500012Q00992Q0100024Q0099010200034Q00030002000100022Q0034000300013Q000ED5000200210001000300044F3Q00210001001269010300043Q00204F0103000300054Q000400013Q00122Q000500066Q00030005000200062Q000300220001000100044F3Q00220001001243000300074Q009901045Q00204D0104000400012Q0034000400043Q000ED50002002F0001000400044F3Q002F0001001269010400043Q0020FE0004000400054Q00055Q00202Q00050005000100122Q000600066Q00040006000200062Q000400300001000100044F3Q00300001001243000400084Q0099010500044Q008A00063Q000300122Q0007000A3Q00122Q0008000B6Q00098Q0008000200024Q00070007000800102Q00060009000700122Q0007000D3Q00202Q00070007000E00122Q0008000F4Q0090010900044Q0083000A00016Q000B00036Q0007000B000200102Q0006000C000700302Q0006001000114Q0005000200016Q00017Q00023Q00030A3Q00466C696768744D6F6465026Q00F03F01044Q00992Q015Q00204D01023Q00020010E10001000100022Q0064012Q00017Q00063Q00030A3Q0043616D6572614D6F646503043Q007479706503053Q007461626C65026Q00F03F030A3Q004175746F4D696E696E6703193Q002043616D657261204D6F6465206368616E67656420746F3A20011A4Q00992Q015Q001269010200024Q009001036Q00310002000200020026DF000200090001000300044F3Q0009000100204D01023Q000400060D0102000A0001000100044F3Q000A00012Q009001025Q0010E10001000100022Q00992Q015Q00204D2Q01000100050006082Q01001300013Q00044F3Q001300012Q00992Q0100014Q00A40001000100012Q00992Q0100024Q00A40001000100012Q00992Q0100033Q0012A2000200066Q00035Q00202Q0003000300014Q0002000200034Q0001000200016Q00017Q00013Q0003093Q004D696E6544656C617901034Q00992Q015Q0010E1000100014Q0064012Q00017Q00013Q00030F3Q004D696E6544656C61794A692Q74657201034Q00992Q015Q0010E1000100014Q0064012Q00017Q00013Q0003103Q00486F72697A6F6E74616C4F2Q6673657401034Q00992Q015Q0010E1000100014Q0064012Q00017Q00013Q0003163Q00526F746174696F6E446561645A6F6E6554726176656C01034Q00992Q015Q0010E1000100014Q0064012Q00017Q001C3Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7303063Q006970616972732Q0103053Q007461626C6503063Q00696E73657274030D3Q0053656C6563746564526F636B73030B3Q0043752Q72656E74526F636B00030E3Q00526F636B5072696F726974696573026Q00F03F03093Q00526F636B4C6162656C028Q0003063Q00636F6E63617403023Q002C20030F3Q00286E6F6E652073656C65637465642903053Q007063612Q6C030E3Q00526F636B436F756E744C6162656C030D3Q005072696F726974794C6162656C2Q033Q003173742Q033Q00326E642Q033Q003372642Q033Q003474682Q033Q003574682Q033Q003674682Q033Q003774682Q033Q0038746803023Q00746803023Q003A2001834Q00902Q016Q009901025Q00204D0102000200010006080102001D00013Q00044F3Q001D00012Q006D01025Q001269010300024Q0099010400014Q001C00030002000500044F3Q000B00010020120002000700030006AA0003000A0001000200044F3Q000A00012Q006D01035Q001269010400024Q009001056Q001C00040002000600044F3Q001A00012Q00C00009000200080006080109001A00013Q00044F3Q001A0001001269010900043Q00204D0109000900052Q0090010A00034Q0090010B00084Q00260109000B00010006AA000400120001000200044F3Q001200012Q00902Q0100034Q009901025Q00105D0102000600014Q000200023Q00302Q0002000700084Q00028Q00035Q00102Q0002000900034Q00025Q00202Q0002000200064Q000200023Q001239010300026Q00045Q00202Q0004000400064Q00030002000500044Q003100012Q009901085Q00204D0108000800092Q007901090002000600207D00090009000A2Q007B0008000700090006AA0003002C0001000200044F3Q002C00012Q0099010300033Q00204D01030003000B0006080103004800013Q00044F3Q00480001000ED5000C00410001000200044F3Q00410001001269010300043Q0020FE00030003000D4Q00045Q00202Q00040004000600122Q0005000E6Q00030005000200062Q000300420001000100044F3Q004200010012430003000F3Q001269010400103Q00068201053Q000100022Q0099012Q00034Q0090012Q00034Q007B0104000200012Q005800036Q0099010300033Q00204D0103000300110006080103005200013Q00044F3Q00520001001269010300103Q00068201040001000100032Q0099012Q00034Q0099012Q00044Q0090012Q00014Q007B0103000200012Q0099010300033Q00204D0103000300120006080103008200013Q00044F3Q00820001000ED5000A007E0001000200044F3Q007E00012Q006D010300083Q001243000400133Q001243000500143Q001243000600153Q001243000700163Q0012DA000800173Q00122Q000900183Q00122Q000A00193Q00122Q000B001A6Q0003000800012Q006D01045Q001239010500026Q00065Q00202Q0006000600064Q00050002000700044Q00750001001269010A00043Q00204D010A000A00052Q0090010B00044Q00C0000C0003000800060D010C00710001000100044F3Q007100012Q0090010C00083Q001243000D001B4Q00ED000C000C000D001243000D001C4Q0090010E00094Q00ED000C000C000E2Q0026010A000C00010006AA000500680001000200044F3Q00680001001269010500103Q00068201060002000100022Q0099012Q00034Q0090012Q00044Q007B0105000200012Q005800035Q00044F3Q00820001001269010300103Q00068201040003000100012Q0099012Q00034Q007B0103000200012Q0064012Q00013Q00043Q00033Q0003093Q00526F636B4C6162656C2Q033Q0053657403013Q002000084Q002E7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q00023Q00030E3Q00526F636B436F756E744C6162656C2Q033Q0053657400084Q00C27Q00206Q000100206Q00024Q000200016Q000300026Q000200039Q0000016Q00017Q00063Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403013Q002003053Q007461626C6503063Q00636F6E63617403023Q002Q20000C4Q00047Q00206Q000100206Q000200122Q000200033Q00122Q000300043Q00202Q0003000300054Q000400013Q00122Q000500066Q0003000500024Q0002000200036Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403203Q002053656C65637420322B20726F636B7320746F20736574207072696F7269747900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00013Q00030F3Q005072696F72697479456E61626C656401034Q00992Q015Q0010E1000100014Q0064012Q00017Q001C3Q00030D3Q0053656C6563746564526F636B73027Q004003053Q005469746C6503083Q005072696F7269747903073Q00436F6E74656E7403163Q0053656C65637420322B20726F636B732066697273742103083Q004475726174696F6E03063Q00697061697273030E3Q00526F636B5072696F726974696573026Q00F03F03053Q007461626C6503063Q00696E7365727403043Q00726F636B03013Q007003043Q00736F72742Q033Q003173742Q033Q00326E642Q033Q003372642Q033Q003474682Q033Q003574682Q033Q003674682Q033Q003774682Q033Q0038746803023Q00746803023Q003A20030D3Q005072696F726974794C6162656C03053Q007063612Q6C030F3Q004F726465722072657665727365642100644Q0099016Q00204D014Q00012Q003400015Q0026242Q01000C0001000200044F3Q000C00012Q00992Q0100014Q003201023Q000300302Q00020003000400302Q00020005000600302Q0002000700024Q0001000200016Q00014Q006D2Q016Q006800025Q00122Q000300086Q00048Q00030002000500044Q001C00012Q009901085Q00204D0108000800092Q00C000080008000700060D010800190001000100044F3Q001900012Q007901080002000600207D00080008000A2Q007901090002000800207D00090009000A2Q007B0001000700090006AA000300120001000200044F3Q001200012Q009901035Q0010E90003000900014Q00035Q00122Q000400086Q00058Q00040002000600044Q002F00010012690109000B3Q00202701090009000C4Q000A00036Q000B3Q000200102Q000B000D00084Q000C5Q00202Q000C000C00094Q000C000C000800102Q000B000E000C4Q0009000B00010006AA000400250001000200044F3Q002500010012690104000B3Q00204D01040004000F2Q0090010500033Q0002B300066Q00560104000600014Q00048Q000500083Q00122Q000600103Q00122Q000700113Q00122Q000800123Q00122Q000900133Q0012DA000A00143Q00122Q000B00153Q00122Q000C00163Q00122Q000D00176Q000500080001001269010600084Q0090010700034Q001C00060002000800044F3Q00520001001269010B000B3Q00204D010B000B000C2Q0090010C00044Q00C0000D0005000900060D010D004E0001000100044F3Q004E00012Q0090010D00093Q001243000E00184Q00ED000D000D000E001243000E00193Q00204D010F000A000D2Q00ED000D000D000F2Q0026010B000D00010006AA000600450001000200044F3Q004500012Q0099010600023Q00204D01060006001A0006080106005D00013Q00044F3Q005D00010012690106001B3Q00068201070001000100022Q0099012Q00024Q0090012Q00044Q007B0106000200012Q0099010600014Q003201073Q000300302Q00070003000400302Q00070005001C00302Q0007000700024Q0006000200016Q00013Q00023Q00013Q0003013Q007002083Q00204D01023Q000100204D010300010001000600010300050001000200044F3Q000500012Q00EF00026Q008B010200014Q00E2000200024Q0064012Q00017Q00063Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403013Q002003053Q007461626C6503063Q00636F6E63617403023Q002Q20000C4Q00047Q00206Q000100206Q000200122Q000200033Q00122Q000300043Q00202Q0003000300054Q000400013Q00122Q000500066Q0003000500024Q0002000200036Q000200016Q00017Q00013Q0003143Q005072696F726974795363616E496E74657276616C01034Q00992Q015Q0010E1000100014Q0064012Q00017Q00013Q0003163Q005072696F72697479537769746368432Q6F6C646F776E01034Q00992Q015Q0010E1000100014Q0064012Q00017Q00013Q0003113Q005072696F726974794477652Q6C54696D6501034Q00992Q015Q0010E1000100014Q0064012Q00017Q00013Q0003143Q005072696F72697479536B6970432Q6F6C646F776E01034Q00992Q015Q0010E1000100014Q0064012Q00017Q000B3Q00030E3Q00526F636B5072696F726974696573030D3Q005072696F726974794C6162656C03053Q007063612Q6C030B3Q0043752Q72656E74526F636B0003053Q005469746C6503083Q005072696F7269747903073Q00436F6E74656E7403123Q005072696F72697469657320636C656172656403083Q004475726174696F6E027Q004000144Q00D19Q0000015Q00104Q000100016Q00013Q00206Q000200064Q000B00013Q00044F3Q000B0001001269012Q00033Q0006822Q013Q000100012Q0099012Q00014Q007B012Q000200012Q0099012Q00023Q00306D3Q000400052Q0099012Q00034Q00322Q013Q000300302Q00010006000700302Q00010008000900302Q0001000A000B6Q000200016Q00013Q00013Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403123Q005072696F72697469657320636C656172656400064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00113Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7303063Q006970616972732Q0103053Q007461626C6503063Q00696E73657274030C3Q0053656C65637465644F726573030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F74696669656403083Q004F72654C6162656C028Q0003063Q00636F6E63617403023Q002C20030F3Q00286E6F6E652073656C65637465642903053Q007063612Q6C014E4Q00902Q016Q009901025Q00204D0102000200010006080102001D00013Q00044F3Q001D00012Q006D01025Q001269010300024Q0099010400014Q001C00030002000500044F3Q000B00010020120002000700030006AA0003000A0001000200044F3Q000A00012Q006D01035Q001269010400024Q009001056Q001C00040002000600044F3Q001A00012Q00C00009000200080006080109001A00013Q00044F3Q001A0001001269010900043Q00204D0109000900052Q0090010A00034Q0090010B00084Q00260109000B00010006AA000400120001000200044F3Q001200012Q00902Q0100034Q009901025Q00103C0102000600014Q000200023Q00302Q0002000700084Q000200026Q00035Q00102Q0002000900034Q000200026Q00035Q00102Q0002000A00034Q000200024Q006D01035Q00104A0002000B00034Q000200026Q00035Q00102Q0002000900034Q000200024Q005900035Q00102Q0002000A00034Q000200026Q00035Q00102Q0002000B00034Q000200033Q00202Q00020002000C00062Q0002004B00013Q00044F3Q004B00012Q009901025Q00204D0102000200062Q0034000200023Q000ED5000D00440001000200044F3Q00440001001269010200043Q0020FE00020002000E4Q00035Q00202Q00030003000600122Q0004000F6Q00020004000200062Q000200450001000100044F3Q00450001001243000200103Q001269010300113Q00068201043Q000100022Q0099012Q00034Q0090012Q00024Q007B0103000200012Q005800026Q0099010200044Q00A40002000100012Q0064012Q00013Q00013Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403183Q00476C6F62616C204F726573202866612Q6C6261636B293A2000084Q002E7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q000F3Q00030C3Q0053656C65637465644F726573030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F746966696564030B3Q004F726544726F70646F776E03053Q007063612Q6C03083Q004F72654C6162656C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403133Q00476C6F62616C206F72657320636C656172656403083Q004475726174696F6E027Q004000274Q0099017Q006D2Q015Q0010E13Q000100012Q0099012Q00013Q00306D3Q000200032Q0099012Q00014Q006D2Q015Q0010E13Q000400012Q0099012Q00014Q005900015Q00104Q000500016Q00016Q00015Q00104Q000600016Q00023Q00206Q000700064Q001600013Q00044F3Q00160001001269012Q00083Q0006822Q013Q000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q0009000608012Q001E00013Q00044F3Q001E0001001269012Q00083Q0006822Q010001000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00034Q00A43Q000100012Q0099012Q00044Q00322Q013Q000300302Q0001000A000B00302Q0001000C000D00302Q0001000E000F6Q000200016Q00013Q00023Q00023Q00030B3Q004F726544726F70646F776E2Q033Q0053657400064Q00067Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403273Q00476C6F62616C204F726573202866612Q6C6261636B293A20286E6F6E652073656C65637465642900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00063Q0003113Q00557365476C6F62616C46612Q6C6261636B030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F74696669656401104Q00992Q015Q00103C2Q0100016Q000100013Q00302Q0001000200034Q000100016Q00025Q00102Q0001000400024Q000100016Q00025Q00102Q0001000500024Q000100014Q002500025Q00102Q0001000600024Q000100026Q0001000100016Q00017Q00013Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7301034Q00992Q015Q0010E1000100014Q0064012Q00017Q00063Q00028Q0003143Q00284E6F20726F636B7320617661696C61626C652903063Q00286E6F6E652903063Q0069706169727303053Q007461626C6503063Q00696E73657274001A4Q0099017Q00347Q000ED50001000700013Q00044F3Q000700012Q0099016Q00060D012Q000A0001000100044F3Q000A00012Q006D012Q00013Q001243000100024Q00053Q000100012Q006D2Q0100013Q001243000200034Q0005000100010001001269010200044Q009001036Q001C00020002000400044F3Q00160001001269010700053Q00204D0107000700062Q0090010800014Q0090010900064Q00260107000900010006AA000200110001000200044F3Q001100012Q00E2000100024Q0064012Q00017Q00063Q00028Q0003133Q002853656C65637420617265612066697273742903063Q00286E6F6E652903063Q0069706169727303053Q007461626C6503063Q00696E73657274001A4Q0099017Q00347Q000ED50001000700013Q00044F3Q000700012Q0099016Q00060D012Q000A0001000100044F3Q000A00012Q006D012Q00013Q001243000100024Q00053Q000100012Q006D2Q0100013Q001243000200034Q0005000100010001001269010200044Q009001036Q001C00020002000400044F3Q00160001001269010700053Q00204D0107000700062Q0090010800014Q0090010900064Q00260107000900010006AA000200110001000200044F3Q001100012Q00E2000100024Q0064012Q00017Q00103Q00026Q00F03F026Q000840030A3Q0046696C746572536C6F7403053Q004C6162656C030E3Q00526F636B4F726546696C7465727303043Q00526F636B03043Q004F726573028Q0003053Q007461626C6503063Q00636F6E63617403023Q002C20026Q003E402Q033Q00737562026Q003B402Q033Q003Q2E03053Q007063612Q6C00483Q0012433Q00013Q001243000100023Q001243000200013Q0004963Q004700012Q009901045Q00124C000500036Q000600033Q00122Q000700046Q0005000500074Q00040004000500062Q0004004500013Q00044F3Q004500012Q0099010500013Q00204D0105000500050006080105001300013Q00044F3Q001300012Q0099010500013Q00204D0105000500052Q00C00005000500030006080105003500013Q00044F3Q0035000100204D0106000500060006080106003500013Q00044F3Q0035000100204D0106000500070006080106003500013Q00044F3Q0035000100204D0106000500072Q0034000600063Q000ED5000800350001000600044F3Q00350001001269010600093Q00206701060006000A00202Q00070005000700122Q0008000B6Q0006000800024Q000700063Q000E2Q000C002D0001000700044F3Q002D000100201801070006000D001262010900013Q00122Q000A000E6Q0007000A000200122Q0008000F6Q000600070008001269010700103Q00068201083Q000100032Q0090012Q00044Q0090012Q00054Q0090012Q00064Q007B0107000200012Q005800065Q00044F3Q004400010006080105004000013Q00044F3Q0040000100204D0106000500060006080106004000013Q00044F3Q00400001001269010600103Q00068201070001000100022Q0090012Q00044Q0090012Q00054Q007B01060002000100044F3Q00440001001269010600103Q00068201070002000100012Q0090012Q00044Q007B0106000200012Q005800056Q005800045Q0004233Q000400012Q0064012Q00013Q00033Q00043Q002Q033Q0053657403043Q00E286922003043Q00526F636B03023Q003A20000A4Q00197Q00206Q000100122Q000200026Q000300013Q00202Q00030003000300122Q000400046Q000500026Q0002000200056Q000200016Q00017Q00043Q002Q033Q0053657403043Q00E286922003043Q00526F636B030B3Q003A20286E6F206F7265732900094Q00F37Q00206Q000100122Q000200026Q000300013Q00202Q00030003000300122Q000400046Q0002000200046Q000200016Q00017Q00023Q002Q033Q00536574030B3Q00E286922028656D7074792900054Q001F7Q00206Q000100122Q000200028Q000200016Q00019Q002Q0001093Q0006822Q013Q000100062Q0099017Q0090017Q0099012Q00014Q0099012Q00024Q0099012Q00034Q0099012Q00044Q00E2000100024Q0064012Q00013Q00013Q00093Q0003043Q007479706503053Q007461626C65026Q00F03F03063Q00286E6F6E6529030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F74696669656401243Q0012692Q0100014Q009001026Q00310001000200020026DF000100080001000200044F3Q0008000100204D2Q013Q000300060D2Q0100090001000100044F3Q000900012Q00902Q015Q0026DF0001000C0001000400044F3Q000C00012Q001A2Q0100014Q009901026Q0020010300016Q0002000200034Q000400026Q000500016Q000600016Q000700036Q0004000700014Q000400033Q00302Q0004000500064Q000400034Q006D01055Q00107E0004000700054Q000400036Q00055Q00102Q0004000800054Q000400036Q00055Q00102Q0004000900054Q000400046Q0004000100014Q000400054Q00A40004000100012Q0064012Q00019Q002Q0001093Q0006822Q013Q000100062Q0099017Q0090017Q0099012Q00014Q0099012Q00024Q0099012Q00034Q0099012Q00044Q00E2000100024Q0064012Q00013Q00013Q000B3Q0003043Q007479706503053Q007461626C6503063Q0069706169727303063Q00286E6F6E6529034Q0003063Q00696E73657274030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F74696669656401343Q0012692Q0100014Q009001026Q00310001000200020026DF000100070001000200044F3Q000700010006332Q01000A00013Q00044F3Q000A00012Q006D2Q0100014Q009001026Q00050001000100012Q006D01025Q001269010300034Q0090010400014Q001C00030002000500044F3Q001A00010006080107001A00013Q00044F3Q001A00010026E50007001A0001000400044F3Q001A00010026E50007001A0001000500044F3Q001A0001001269010800023Q00204D0108000800062Q0090010900024Q0090010A00074Q00260108000A00010006AA0003000F0001000200044F3Q000F00012Q009901036Q0020010400016Q0003000200044Q000500026Q000600016Q000700036Q000800026Q0005000800014Q000500033Q00302Q0005000700084Q000500034Q006D01065Q00107E0005000900064Q000500036Q00065Q00102Q0005000A00064Q000500036Q00065Q00102Q0005000B00064Q000500046Q0005000100014Q000500054Q00A40005000100012Q0064012Q00017Q00113Q00026Q00F03F026Q000840030A3Q0046696C746572536C6F7403043Q00526F636B2Q033Q004F726503053Q007063612Q6C030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F74696669656403053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403183Q00412Q6C20736C6F742066696C7465727320636C656172656403083Q004475726174696F6E027Q004000393Q0012433Q00013Q001243000100023Q001243000200013Q0004963Q002300012Q009901046Q002C010500036Q000600066Q00078Q0004000700014Q000400013Q00122Q000500036Q000600033Q00122Q000700046Q0005000500074Q0004000400054Q000500013Q00122Q000600036Q000700033Q00122Q000800056Q0006000600084Q00050005000600062Q0004001B00013Q00044F3Q001B0001001269010600063Q00068201073Q000100012Q0090012Q00044Q007B0106000200010006080105002100013Q00044F3Q00210001001269010600063Q00068201070001000100012Q0090012Q00054Q007B0106000200012Q005800045Q0004233Q000400012Q0099012Q00023Q0030823Q000700086Q00026Q00015Q00104Q000900016Q00026Q00015Q00104Q000A00016Q00026Q00015Q00104Q000B00012Q0099012Q00034Q00A43Q000100012Q0099012Q00044Q00A43Q000100012Q0099012Q00054Q00322Q013Q000300302Q0001000C000D00302Q0001000E000F00302Q0001001000116Q000200016Q00013Q00023Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q00777Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q0026012Q000200012Q0064012Q00017Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q00777Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q0026012Q000200012Q0064012Q00017Q00203Q00026Q00F03F03093Q0048656176656E697465027Q0040030A3Q0047617267616E7475616E03083Q00537572796166616C030B3Q00457468657265616C697465026Q00084003063Q00286E6F6E6529030A3Q0046696C746572536C6F742Q033Q004F726503053Q007063612Q6C03053Q007461626C6503063Q00696E7365727403083Q00746F737472696E67028Q0003053Q005469746C65030E3Q00536C6F742054656D706C6174657303073Q00436F6E74656E7403173Q005069636B20726F636B20666F7220736C6F742873293A2003063Q00636F6E63617403023Q002C2003083Q004475726174696F6E030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F74696669656403123Q00412Q706C69656420746F20736C6F74733A2003193Q004D692Q73696E6720726F636B20696E20736C6F742873293A2003163Q00536C6F742054656D706C6174657320412Q706C69656403013Q000A026Q00104000884Q00679Q00000100018Q000200018Q00034Q000100013Q00122Q000200026Q0001000100010010E13Q000100012Q00722Q0100033Q00122Q000200043Q00122Q000300053Q00122Q000400066Q0001000300010010E13Q000300012Q006D2Q0100023Q001243000200043Q001243000300054Q00050001000200010010E13Q000700012Q005600018Q00025Q00122Q000300013Q00122Q000400073Q00122Q000500013Q00042Q0003004500012Q0099010700014Q0090010800064Q001C0007000200080006080107003C00013Q00044F3Q003C00010026E50007003C0001000800044F3Q003C00012Q0099010900024Q0052010A00066Q000B00076Q000C3Q00064Q0009000C00014Q000900033Q00124C000A00096Q000B00063Q00122Q000C000A6Q000A000A000C4Q00090009000A00062Q0009003300013Q00044F3Q00330001001269010A000B3Q000682010B3Q000100032Q0090012Q00094Q0090017Q0090012Q00064Q007B010A00020001001269010A000C3Q002035000A000A000D4Q000B00013Q00122Q000C000E6Q000D00066Q000C000D6Q000A3Q00012Q005800095Q00044F3Q004300010012690109000C3Q00203500090009000D4Q000A00023Q00122Q000B000E6Q000C00066Q000B000C6Q00093Q00012Q005800065Q0004230003001900012Q0034000300013Q0026DF000300560001000F00044F3Q005600012Q0099010300044Q00AC00043Q000300302Q00040010001100122Q000500133Q00122Q0006000C3Q00202Q0006000600144Q000700023Q00122Q000800156Q0006000800024Q00050005000600102Q00040012000500306D0004001600072Q007B0103000200012Q0064012Q00014Q0099010300053Q0030820003001700184Q000300056Q00045Q00102Q0003001900044Q000300056Q00045Q00102Q0003001A00044Q000300056Q00045Q00102Q0003001B00042Q0099010300064Q00F10003000100014Q000300076Q0003000100014Q000300013Q00122Q0004001C3Q00122Q0005000C3Q00202Q0005000500144Q000600013Q00122Q000700156Q0005000700022Q00ED0004000400052Q00050003000100012Q0034000400023Q000ED5000F007C0001000400044F3Q007C00010012690104000C3Q0020A800040004000D4Q000500033Q00122Q0006001D3Q00122Q0007000C3Q00202Q0007000700144Q000800023Q00122Q000900156Q0007000900024Q0006000600074Q0004000600012Q0099010400044Q002900053Q000300302Q00050010001E00122Q0006000C3Q00202Q0006000600144Q000700033Q00122Q0008001F6Q00060008000200102Q00050012000600302Q0005001600204Q0004000200012Q0064012Q00013Q00013Q00013Q002Q033Q0053657400074Q00387Q00206Q00014Q000200016Q000300026Q0002000200036Q000200016Q00017Q00203Q0003043Q007479706503053Q007461626C65026Q00F03F028Q0003063Q006970616972732Q0103063Q00696E7365727403193Q004175746F5472696D496E76616C696453656C656374696F6E7303053Q005469746C65030D3Q004F72652054656D706C6174657303073Q00436F6E74656E7403283Q004F7265206C697374206E6F742072656164793B20612Q706C69656420776974686F7574207472696D03083Q004475726174696F6E026Q000840030C3Q0053656C65637465644F726573030B3Q004F726544726F70646F776E03053Q007063612Q6C03083Q004F72654C6162656C03063Q00636F6E63617403023Q002C20030F3Q00286E6F6E652073656C656374656429030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B73030F3Q004F7265536B69704E6F74696669656403063Q00286E6F6E652903193Q0054656D706C61746520412Q706C6965642028476C6F62616C2903013Q000A03053Q007072696E74032F3Q005B466F726765204D696E696E675D204F72652054656D706C61746520412Q706C69656420746F20474C4F42414C3A2003093Q00207C204F7265733A20019B3Q0012692Q0100014Q009001026Q00310001000200020026DF000100080001000200044F3Q0008000100204D2Q013Q000300060D2Q0100090001000100044F3Q000900012Q00902Q015Q0006082Q01000F00013Q00044F3Q000F00012Q009901026Q00C000020002000100060D010200100001000100044F3Q001000012Q0064012Q00014Q009901026Q007F0002000200014Q000300016Q000400016Q0003000200014Q000300026Q000300033Q000E2Q0004001A0001000300044F3Q001A00012Q00EF00036Q008B010300014Q006D01045Q0006080103002500013Q00044F3Q00250001001269010500054Q0099010600024Q001C00050002000700044F3Q002300010020120004000900060006AA000500220001000200044F3Q002200012Q006D01055Q0006080103003600013Q00044F3Q00360001001269010600054Q0090010700024Q001C00060002000800044F3Q003400012Q00C0000B0004000A000608010B003400013Q00044F3Q00340001001269010B00023Q00204D010B000B00072Q0090010C00054Q0090010D000A4Q0026010B000D00010006AA0006002C0001000200044F3Q002C00012Q0090010600024Q0099010700033Q00204D0107000700080006080107003F00013Q00044F3Q003F00010006080103003F00013Q00044F3Q003F00012Q0090010600053Q00044F3Q004B00012Q0099010700033Q00204D0107000700080006080107004B00013Q00044F3Q004B000100060D0103004B0001000100044F3Q004B00012Q0099010700044Q001D00083Q000300302Q00080009000A00302Q0008000B000C00302Q0008000D000E4Q0007000200012Q0099010700033Q0010E10007000F00062Q0099010700053Q00204D0107000700100006080107005600013Q00044F3Q00560001001269010700113Q00068201083Q000100022Q0099012Q00054Q0099012Q00034Q007B0107000200012Q0099010700053Q00204D0107000700120006080107006E00013Q00044F3Q006E00012Q0099010700033Q00204D01070007000F2Q0034000700073Q000ED5000400670001000700044F3Q00670001001269010700023Q0020FE0007000700134Q000800033Q00202Q00080008000F00122Q000900146Q00070009000200062Q000700680001000100044F3Q00680001001243000700153Q001269010800113Q00068201090001000100022Q0099012Q00054Q0090012Q00074Q007B0108000200012Q005800076Q0099010700063Q0030A50007001600174Q000700066Q00085Q00102Q0007001800084Q000700066Q00085Q00102Q0007001900084Q000700066Q00085Q00102Q0007001A00084Q000700076Q0007000100014Q000700033Q00202Q00070007000F4Q000700073Q000E2Q000400880001000700044F3Q00880001001269010700023Q0020FE0007000700134Q000800033Q00202Q00080008000F00122Q000900146Q00070009000200062Q000700890001000100044F3Q008900010012430007001B4Q0099010800044Q009500093Q000300302Q00090009001C4Q000A00013Q00122Q000B001D6Q000C00076Q000A000A000C00102Q0009000B000A00302Q0009000D000E4Q00080002000100122Q0008001E3Q00122Q0009001F6Q000A00013Q00122Q000B00206Q000C00076Q00090009000C4Q0008000200016Q00013Q00023Q00033Q00030B3Q004F726544726F70646F776E2Q033Q00536574030C3Q0053656C65637465644F72657300074Q00A67Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403183Q00476C6F62616C204F726573202866612Q6C6261636B293A2000084Q002E7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q00013Q00030F3Q004F7265436865636B456E61626C656401034Q00992Q015Q0010E1000100014Q0064012Q00017Q00013Q00030D3Q004F7265536B69704E6F7469667901034Q00992Q015Q0010E1000100014Q0064012Q00017Q00033Q0003143Q00412Q6C6F774F726546696C746572427970612Q7303153Q0049676E6F72654F726546696C74657273556E74696C028Q0001074Q00992Q015Q0010E1000100013Q00060D012Q00060001000100044F3Q000600012Q00992Q0100013Q00306D0001000200032Q0064012Q00017Q003A3Q00030A3Q004175746F4D696E696E67010003103Q004175746F4D696E696E67546F2Q676C6503053Q007063612Q6C03053Q00706169727303043Q007479706503053Q007461626C65030E3Q00526F636B4F726546696C7465727303103Q004C61737446696C746572536F7572636500030E3Q004C61737446696C746572526F636B030D3Q004E6F54617267657453696E636503153Q0049676E6F72654F726546696C74657273556E74696C028Q00030B3Q0043752Q72656E74526F636B030C3Q0043752Q72656E745068617365030A3Q00536B69704672616D6573030E3Q00536B69704D696E654672616D6573030D3Q004C6F636B65644D696E65506F73030A3Q00546F74616C4D696E656403103Q004D61696E74656E616E6365436F756E74030E3Q004C6173744C2Q6F6B546172676574030E3Q004C617374526F636B536561726368030D3Q004C6173744E6F526F636B4C6F67030D3Q004C617374536B69705265736574030C3Q00536B692Q706564526F636B7303103Q004F726546696C7465726564526F636B7303113Q004C6173744F7265536B69704E6F74696679030F3Q004F7265536B69704E6F74696669656403153Q004C617374416C72656164794D696E696E6754696D65030D3Q0050656E64696E6753776974636803113Q004C61737450656E64696E67537769746368030A3Q004C617374526F636B4850030B3Q004C617374526F636B52656603123Q004D696E657353696E636548504368616E6765030E3Q00537475636B436865636B54696D65030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D65030E3Q004C32412Q74656D7074436F756E74030B3Q004465627567546F2Q676C65030E3Q004F7265436865636B546F2Q676C6503133Q004F7265536B69704E6F74696679546F2Q676C6503153Q004F726546696C746572427970612Q73546F2Q676C6503173Q00557365476C6F62616C46612Q6C6261636B546F2Q676C65030B3Q004F726544726F70646F776E03083Q004F72654C6162656C03113Q0041637469766546696C7465724C6162656C030E3Q0046696C746572536C6F74314F7265030E3Q0046696C746572536C6F74324F7265030E3Q0046696C746572536C6F74334F726503123Q00526F636B4F726546696C7465724C6162656C03133Q00416374697665526F636B4F726546696C74657203073Q0044657374726F7903023Q005F4703053Q00466F726765030D3Q0052657365744D696E696E67554903053Q007072696E7403223Q005B466F726765204D696E696E675D2046752Q6C20526573657420436F6D706C65746500E04Q0099016Q00306D3Q000100022Q0099012Q00014Q00A43Q000100012Q0099012Q00023Q00204D014Q0003000608012Q000C00013Q00044F3Q000C0001001269012Q00043Q0006822Q013Q000100012Q0099012Q00024Q007B012Q00020001001269012Q00054Q00992Q0100034Q001C3Q0002000200044F3Q00240001001269010500064Q0090010600044Q00310005000200020026DF000500220001000700044F3Q002200012Q009901056Q00F500068Q00050003000600122Q000500056Q000600046Q00050002000700044Q001F00012Q0099010A6Q00C0000A000A00032Q007B000A000800090006AA0005001C0001000200044F3Q001C000100044F3Q002400012Q009901056Q007B0005000300040006AA3Q00100001000200044F3Q001000012Q0099017Q00BE00015Q00104Q000800016Q00043Q00304Q0009000A6Q00043Q00304Q000B000A6Q00043Q00304Q000C000A6Q00043Q00304Q000D000E6Q00043Q00304Q000F000A6Q00043Q00304Q0010000E6Q00043Q00304Q0011000E6Q00043Q00304Q0012000E6Q00043Q00304Q0013000A6Q00043Q00304Q0014000E6Q00043Q00304Q0015000E6Q00043Q00304Q0016000A6Q00043Q00304Q0017000A6Q00043Q00304Q0018000A6Q00043Q00304Q0019000E6Q00046Q00015Q00104Q001A00016Q00046Q00015Q00104Q001B00016Q00043Q00304Q001C000E6Q00046Q00015Q00104Q001D00016Q00043Q00304Q001E000E6Q00043Q00304Q001F00026Q00043Q00304Q0020000E6Q00043Q00304Q0021000A6Q00043Q00304Q0022000A6Q00043Q00304Q0023000E6Q00043Q00304Q0024000E6Q00043Q00304Q0025000E6Q00043Q00304Q0026000E6Q00043Q00304Q0027000E6Q00023Q00206Q002800064Q006E00013Q00044F3Q006E0001001269012Q00043Q0006822Q010001000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q0029000608012Q007700013Q00044F3Q00770001001269012Q00043Q0006822Q010002000100022Q0099012Q00024Q0099012Q00034Q007B012Q000200012Q0099012Q00023Q00204D014Q002A000608012Q008000013Q00044F3Q00800001001269012Q00043Q0006822Q010003000100022Q0099012Q00024Q0099012Q00034Q007B012Q000200012Q0099012Q00023Q00204D014Q002B000608012Q008900013Q00044F3Q00890001001269012Q00043Q0006822Q010004000100022Q0099012Q00024Q0099012Q00034Q007B012Q000200012Q0099012Q00023Q00204D014Q002C000608012Q009200013Q00044F3Q00920001001269012Q00043Q0006822Q010005000100022Q0099012Q00024Q0099012Q00034Q007B012Q000200012Q0099012Q00023Q00204D014Q002D000608012Q009A00013Q00044F3Q009A0001001269012Q00043Q0006822Q010006000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q002E000608012Q00A200013Q00044F3Q00A20001001269012Q00043Q0006822Q010007000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q002F000608012Q00AA00013Q00044F3Q00AA0001001269012Q00043Q0006822Q010008000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q0030000608012Q00B200013Q00044F3Q00B20001001269012Q00043Q0006822Q010009000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q0031000608012Q00BA00013Q00044F3Q00BA0001001269012Q00043Q0006822Q01000A000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q0032000608012Q00C200013Q00044F3Q00C20001001269012Q00043Q0006822Q01000B000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00204D014Q0033000608012Q00CA00013Q00044F3Q00CA0001001269012Q00043Q0006822Q01000C000100012Q0099012Q00024Q007B012Q000200012Q0099012Q00023Q00306D3Q0034000A2Q0099012Q00053Q000608012Q00D400013Q00044F3Q00D400012Q0099012Q00053Q002018014Q00352Q007B012Q000200012Q001A017Q0097012Q00053Q001269012Q00363Q00204D014Q003700204D014Q0038000608012Q00DC00013Q00044F3Q00DC0001001269012Q00043Q0002B30001000D4Q007B012Q00020001001269012Q00393Q0012430001003A4Q007B012Q000200012Q0064012Q00013Q000E3Q00023Q0003103Q004175746F4D696E696E67546F2Q676C652Q033Q0053657400064Q0019016Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030B3Q004465627567546F2Q676C652Q033Q0053657400064Q0019016Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q00030E3Q004F7265436865636B546F2Q676C652Q033Q00536574030F3Q004F7265436865636B456E61626C656400074Q00A67Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003133Q004F7265536B69704E6F74696679546F2Q676C652Q033Q00536574030D3Q004F7265536B69704E6F7469667900074Q00A67Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003153Q004F726546696C746572427970612Q73546F2Q676C652Q033Q0053657403143Q00412Q6C6F774F726546696C746572427970612Q7300074Q00A67Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003173Q00557365476C6F62616C46612Q6C6261636B546F2Q676C652Q033Q0053657403113Q00557365476C6F62616C46612Q6C6261636B00074Q00A67Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00023Q00030B3Q004F726544726F70646F776E2Q033Q0053657400064Q00067Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403273Q00476C6F62616C204F726573202866612Q6C6261636B293A20286E6F6E652073656C65637465642900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403133Q004163746976652046696C7465723A204E6F6E6500064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030E3Q0046696C746572536C6F74314F72652Q033Q0053657403063Q00286E6F6E652900084Q004B7Q00206Q000100206Q00024Q000200013Q00122Q000300036Q0002000100012Q0026012Q000200012Q0064012Q00017Q00033Q00030E3Q0046696C746572536C6F74324F72652Q033Q0053657403063Q00286E6F6E652900084Q004B7Q00206Q000100206Q00024Q000200013Q00122Q000300036Q0002000100012Q0026012Q000200012Q0064012Q00017Q00033Q00030E3Q0046696C746572536C6F74334F72652Q033Q0053657403063Q00286E6F6E652900084Q004B7Q00206Q000100206Q00024Q000200013Q00122Q000300036Q0002000100012Q0026012Q000200012Q0064012Q00017Q00033Q0003123Q00526F636B4F726546696C7465724C6162656C2Q033Q00536574030B3Q00287069636B20726F636B2900064Q00C87Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003023Q005F4703053Q00466F726765030D3Q0052657365744D696E696E67554900053Q00125B3Q00013Q00206Q000200206Q00036Q000100016Q00017Q00043Q00030A3Q004175746F4D696E696E67010003103Q004175746F4D696E696E67546F2Q676C6503053Q007063612Q6C00194Q0099016Q00204D014Q000100060D012Q000A0001000100044F3Q000A00012Q0099012Q00014Q00992Q0100024Q00313Q0002000200060D012Q000A0001000100044F3Q000A00012Q0064012Q00014Q0099016Q0030EE3Q000100026Q00038Q000100016Q00048Q000100016Q00053Q00206Q000300064Q001800013Q00044F3Q00180001001269012Q00043Q0006822Q013Q000100012Q0099012Q00054Q007B012Q000200012Q0064012Q00013Q00013Q00023Q0003103Q004175746F4D696E696E67546F2Q676C652Q033Q0053657400064Q0019016Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00", GetFEnv(), ...);
