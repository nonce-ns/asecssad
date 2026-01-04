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
				if (Enum <= 140) then
					if (Enum <= 69) then
						if (Enum <= 34) then
							if (Enum <= 16) then
								if (Enum <= 7) then
									if (Enum <= 3) then
										if (Enum <= 1) then
											if (Enum == 0) then
												local A;
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A]();
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Upvalues[Inst[3]] = Stk[Inst[2]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												do
													return Stk[A], Stk[A + 1];
												end
											else
												local A = Inst[2];
												do
													return Stk[A], Stk[A + 1];
												end
											end
										elseif (Enum > 2) then
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
											Stk[Inst[2]][Inst[3]] = Inst[4];
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
											local A;
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
											Stk[Inst[2]] = Env[Inst[3]];
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
											Stk[Inst[2]] = Env[Inst[3]];
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
											if (Stk[Inst[2]] == Inst[4]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 5) then
										if (Enum > 4) then
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											for Idx = Inst[2], Inst[3] do
												Stk[Idx] = nil;
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
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
										end
									elseif (Enum == 6) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									else
										local B;
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
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum <= 11) then
									if (Enum <= 9) then
										if (Enum == 8) then
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
										end
									elseif (Enum > 10) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										local A;
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
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
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
									end
								elseif (Enum <= 13) then
									if (Enum == 12) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
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
										Stk[Inst[2]] = Inst[3] ~= 0;
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
								elseif (Enum <= 14) then
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
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								elseif (Enum > 15) then
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
									Stk[Inst[2]]();
								end
							elseif (Enum <= 25) then
								if (Enum <= 20) then
									if (Enum <= 18) then
										if (Enum == 17) then
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
											local A;
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
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
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
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum > 19) then
										local A;
										local K;
										local B;
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
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 22) then
									if (Enum > 21) then
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
								elseif (Enum <= 23) then
									local Edx;
									local Results;
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
								elseif (Enum > 24) then
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
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								else
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
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 29) then
								if (Enum <= 27) then
									if (Enum > 26) then
										local Edx;
										local Results;
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
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
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
								elseif (Enum > 28) then
									local B;
									local T;
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
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 31) then
								if (Enum > 30) then
									local B;
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
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								end
							elseif (Enum <= 32) then
								local B;
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
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 33) then
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 51) then
							if (Enum <= 42) then
								if (Enum <= 38) then
									if (Enum <= 36) then
										if (Enum == 35) then
											local A;
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
											if (Stk[Inst[2]] == Inst[4]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum == 37) then
										local Edx;
										local Results;
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
								elseif (Enum <= 40) then
									if (Enum == 39) then
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
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A], Stk[A + 1];
										end
									end
								elseif (Enum == 41) then
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
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
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
									local B;
									local T;
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
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 46) then
								if (Enum <= 44) then
									if (Enum == 43) then
										local B;
										local T;
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
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
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
								elseif (Enum == 45) then
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
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								end
							elseif (Enum <= 48) then
								if (Enum == 47) then
									local A;
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
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
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
							elseif (Enum <= 49) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 50) then
								local B;
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 60) then
							if (Enum <= 55) then
								if (Enum <= 53) then
									if (Enum == 52) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
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
										A = Inst[2];
										Stk[A](Stk[A + 1]);
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
										Stk[Inst[2]] = Inst[3] ~= 0;
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
										local T;
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
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum > 54) then
									Stk[Inst[2]] = Inst[3] ~= 0;
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
								else
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum <= 57) then
								if (Enum == 56) then
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
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 58) then
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
							elseif (Enum > 59) then
								local B;
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local A;
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
								Stk[Inst[2]] = Env[Inst[3]];
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
							end
						elseif (Enum <= 64) then
							if (Enum <= 62) then
								if (Enum == 61) then
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
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
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
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 63) then
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local Edx;
								local Results;
								local A;
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
							end
						elseif (Enum <= 66) then
							if (Enum == 65) then
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
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
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
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 67) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 68) then
							VIP = Inst[3];
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
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 104) then
						if (Enum <= 86) then
							if (Enum <= 77) then
								if (Enum <= 73) then
									if (Enum <= 71) then
										if (Enum == 70) then
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
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
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
											if (Stk[Inst[2]] ~= Inst[4]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum > 72) then
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
										local B;
										local T;
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
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum <= 75) then
									if (Enum > 74) then
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
									end
								elseif (Enum > 76) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Stk[Inst[4]]];
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
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local Edx;
									local Limit;
									local Results;
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
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
									A = Inst[2];
									Results = {Stk[A]()};
									Limit = Inst[4];
									Edx = 0;
									for Idx = A, Limit do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 81) then
								if (Enum <= 79) then
									if (Enum > 78) then
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
									else
										local B;
										local A;
										A = Inst[2];
										Stk[A](Stk[A + 1]);
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
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum == 80) then
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
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								end
							elseif (Enum <= 83) then
								if (Enum == 82) then
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
									Upvalues[Inst[3]] = Stk[Inst[2]];
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
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum <= 84) then
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
							elseif (Enum > 85) then
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
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 95) then
							if (Enum <= 90) then
								if (Enum <= 88) then
									if (Enum > 87) then
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
										Stk[Inst[2]] = Stk[Inst[3]];
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
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum == 89) then
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
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 92) then
								if (Enum > 91) then
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
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 93) then
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
							elseif (Enum > 94) then
								local B;
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
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
						elseif (Enum <= 99) then
							if (Enum <= 97) then
								if (Enum == 96) then
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
							elseif (Enum > 98) then
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							end
						elseif (Enum <= 101) then
							if (Enum > 100) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 102) then
							local B;
							local T;
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
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						elseif (Enum == 103) then
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
								if (Mvm[1] == 91) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 122) then
						if (Enum <= 113) then
							if (Enum <= 108) then
								if (Enum <= 106) then
									if (Enum == 105) then
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
										Stk[Inst[2]] = Env[Inst[3]];
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
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Enum == 107) then
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
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
								elseif (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 110) then
								if (Enum > 109) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
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
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
							elseif (Enum <= 111) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							elseif (Enum > 112) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
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
							end
						elseif (Enum <= 117) then
							if (Enum <= 115) then
								if (Enum == 114) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
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
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum > 116) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Stk[Inst[4]]];
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 119) then
							if (Enum == 118) then
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
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 120) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 121) then
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
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
					elseif (Enum <= 131) then
						if (Enum <= 126) then
							if (Enum <= 124) then
								if (Enum > 123) then
									Stk[Inst[2]] = not Stk[Inst[3]];
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 125) then
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
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
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
							end
						elseif (Enum <= 128) then
							if (Enum > 127) then
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							end
						elseif (Enum <= 129) then
							local B;
							local T;
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
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						elseif (Enum == 130) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
					elseif (Enum <= 135) then
						if (Enum <= 133) then
							if (Enum == 132) then
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
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
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum == 134) then
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
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 137) then
						if (Enum > 136) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
					elseif (Enum <= 138) then
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
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 139) then
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
					else
						local A;
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
					end
				elseif (Enum <= 211) then
					if (Enum <= 175) then
						if (Enum <= 157) then
							if (Enum <= 148) then
								if (Enum <= 144) then
									if (Enum <= 142) then
										if (Enum > 141) then
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
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
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
									elseif (Enum == 143) then
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
										local B;
										local T;
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
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum <= 146) then
									if (Enum > 145) then
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
									else
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
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
										A = Inst[2];
										Stk[A](Stk[A + 1]);
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
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
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
									end
								elseif (Enum == 147) then
									local B;
									local T;
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
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								elseif (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 152) then
								if (Enum <= 150) then
									if (Enum > 149) then
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
									else
										local B = Stk[Inst[4]];
										if B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									end
								elseif (Enum == 151) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 154) then
								if (Enum > 153) then
									local Edx;
									local Results;
									local A;
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
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 155) then
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif (Enum > 156) then
								local K;
								local B;
								local A;
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
								Stk[A](Stk[A + 1]);
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
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 166) then
							if (Enum <= 161) then
								if (Enum <= 159) then
									if (Enum == 158) then
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
										local B;
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
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									end
								elseif (Enum > 160) then
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
							elseif (Enum <= 163) then
								if (Enum > 162) then
									local B;
									local T;
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
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
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
							elseif (Enum <= 164) then
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							elseif (Enum == 165) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
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
						elseif (Enum <= 170) then
							if (Enum <= 168) then
								if (Enum > 167) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
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
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
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
							elseif (Enum == 169) then
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
							end
						elseif (Enum <= 172) then
							if (Enum == 171) then
								local A;
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
								Stk[Inst[2]] = not Stk[Inst[3]];
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
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 173) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
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
							Stk[Inst[2]] = Inst[3];
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
							VIP = Inst[3];
						elseif (Enum == 174) then
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						end
					elseif (Enum <= 193) then
						if (Enum <= 184) then
							if (Enum <= 179) then
								if (Enum <= 177) then
									if (Enum > 176) then
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								elseif (Enum == 178) then
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
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
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
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 181) then
								if (Enum == 180) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
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
							elseif (Enum <= 182) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
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
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 183) then
								local B;
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
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
								do
									return;
								end
							end
						elseif (Enum <= 188) then
							if (Enum <= 186) then
								if (Enum == 185) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum > 187) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
							else
								local B;
								local T;
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
								Stk[Inst[2]] = {};
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 190) then
							if (Enum > 189) then
								local A;
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
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 191) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						elseif (Enum > 192) then
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
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
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 202) then
						if (Enum <= 197) then
							if (Enum <= 195) then
								if (Enum > 194) then
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
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local Edx;
									local Results;
									local A;
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
								end
							elseif (Enum > 196) then
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
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
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
						elseif (Enum <= 199) then
							if (Enum > 198) then
								local B;
								local T;
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum <= 200) then
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
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						elseif (Enum == 201) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
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
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 206) then
						if (Enum <= 204) then
							if (Enum == 203) then
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
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
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
							end
						elseif (Enum == 205) then
							local B;
							local T;
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
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 208) then
						if (Enum > 207) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
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
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 209) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 210) then
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
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Inst[2] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 246) then
					if (Enum <= 228) then
						if (Enum <= 219) then
							if (Enum <= 215) then
								if (Enum <= 213) then
									if (Enum > 212) then
										local A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
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
								elseif (Enum == 214) then
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
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
							elseif (Enum <= 217) then
								if (Enum > 216) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
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
							elseif (Enum == 218) then
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
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 223) then
							if (Enum <= 221) then
								if (Enum == 220) then
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
									local A = Inst[2];
									Stk[A] = Stk[A]();
								end
							elseif (Enum > 222) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
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
						elseif (Enum <= 225) then
							if (Enum > 224) then
								local B;
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
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
							end
						elseif (Enum <= 226) then
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
						elseif (Enum == 227) then
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 237) then
						if (Enum <= 232) then
							if (Enum <= 230) then
								if (Enum > 229) then
									Stk[Inst[2]] = {};
								else
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
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
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum == 231) then
								local B;
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							end
						elseif (Enum <= 234) then
							if (Enum > 233) then
								local B;
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
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
						elseif (Enum <= 235) then
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
						elseif (Enum == 236) then
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
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 241) then
						if (Enum <= 239) then
							if (Enum == 238) then
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
							else
								local A;
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 240) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
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
						else
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
						end
					elseif (Enum <= 243) then
						if (Enum == 242) then
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
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum <= 244) then
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
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
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 245) then
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
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local B;
						local A;
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
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
				elseif (Enum <= 264) then
					if (Enum <= 255) then
						if (Enum <= 250) then
							if (Enum <= 248) then
								if (Enum > 247) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								end
							elseif (Enum > 249) then
								local A = Inst[2];
								local Results = {Stk[A]()};
								local Limit = Inst[4];
								local Edx = 0;
								for Idx = A, Limit do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
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
						elseif (Enum <= 252) then
							if (Enum == 251) then
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
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 253) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Enum == 254) then
							local A;
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
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
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
					elseif (Enum <= 259) then
						if (Enum <= 257) then
							if (Enum > 256) then
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
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum > 258) then
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
							local K;
							local B;
							local A;
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
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 261) then
						if (Enum > 260) then
							local Edx;
							local Results;
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
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 262) then
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					elseif (Enum > 263) then
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
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
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
					end
				elseif (Enum <= 273) then
					if (Enum <= 268) then
						if (Enum <= 266) then
							if (Enum > 265) then
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
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum > 267) then
							Stk[Inst[2]] = Env[Inst[3]];
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
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 270) then
						if (Enum > 269) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A;
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
							Stk[Inst[2]] = not Stk[Inst[3]];
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
					elseif (Enum <= 271) then
						local A;
						local K;
						local B;
						Stk[Inst[2]] = Env[Inst[3]];
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
						Stk[Inst[2]] = Env[Inst[3]];
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
					elseif (Enum > 272) then
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
				elseif (Enum <= 277) then
					if (Enum <= 275) then
						if (Enum == 274) then
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
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum > 276) then
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
					else
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					end
				elseif (Enum <= 279) then
					if (Enum > 278) then
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Inst[3] do
							Insert(T, Stk[Idx]);
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
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 280) then
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
					Stk[Inst[2]] = Inst[3] ~= 0;
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
				elseif (Enum > 281) then
					Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
				else
					local A;
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
					A = Inst[2];
					Stk[A](Stk[A + 1]);
					VIP = VIP + 1;
					Inst = Instr[VIP];
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!38012Q0003023Q006F7303053Q00636C6F636B03043Q007461736B03043Q0077616974026Q00E03F03023Q005F4703053Q00466F72676503043Q005461627303063Q00506C6179657203083Q005261796669656C64026Q00244003043Q007761726E032C3Q005B53652Q6C5D20446570656E64656E63696573206E6F742072656164793B2061626F7274696E67206C6F616403043Q0067616D65030A3Q004765745365727669636503073Q00506C617965727303113Q005265706C69636174656453746F72616765030A3Q0052756E53657276696365030A3Q004775695365727669636503093Q00576F726B7370616365030B3Q004C6F63616C506C6179657203083Q004175746F53652Q6C0100030C3Q0053652Q6C496E74657276616C026Q003E40030D3Q00536B69704661766F72697465732Q0103143Q004E6F54656C65706F72744166746572466972737403093Q0044656275674D6F646503083Q0053652Q6C4F726573030C3Q0053652Q6C452Q73656E63657303093Q0053652Q6C52756E6573030D3Q004F726546696C7465724C69737403113Q00452Q73656E636546696C7465724C697374030E3Q0052756E6546696C7465724C69737403143Q0052756E655175616C6974795468726573686F6C64028Q0003113Q005374726963745175616C6974794D6F646503053Q007061697273030A3Q0053652Q6C436F6E66696703113Q0053652Q6C44656661756C74436F6E666967030E3Q00436861726163746572412Q64656403073Q00436F2Q6E656374026Q003440026Q000CC0026Q00204003083Q004F6273696469616E030E3Q004F72616E6765204372797374616C03083Q00506C6174696E756D03073Q00502Q6F70697465030F3Q00507269736D6174696320486561727403063Q0050756D69636503063Q0051756172747A030F3Q005261696E626F77204372797374616C03083Q00526976616C69746503043Q005275627903073Q0053616E63746973030A3Q0053616E642053746F6E6503083Q0053612Q706869726503093Q005363682Q656C69746503063Q0053696C76657203073Q00536C696D69746503073Q00536E6F7769746503073Q0053746172697465030C3Q0053746F6C656E20486561727403053Q0053746F6E6503063Q0053756C66757203083Q00537572796166616C030A3Q00546964652043617276652Q033Q0054696E03083Q00546974616E69756D03053Q00546F70617A03083Q0054756E677374656E03073Q005572616E69756D03073Q0056616E65676F7303083Q0056656C6368697265030B3Q00566F69646672616374616C03083Q00566F696473746172030D3Q00566F6C63616E696320526F636B03063Q00562Q6F697465030A3Q005965746920486561727403073Q005A657068797465030C3Q00416574686572204C6F74757303083Q00416574686572697403043Q004169746503083Q00416D65746879737403073Q004171756A616465030E3Q00417263616E65204372797374616C03083Q0042616E616E697465030C3Q00426C7565204372797374616C03073Q00426F6E65697465030C3Q0043617264626F61726469746503063Q0043657969746503063Q00436F62616C7403073Q00436F696E69746503063Q00436F2Q706572030F3Q004372696D736F6E204372797374616C030A3Q004372696D736F6E69746503073Q004372797074657803073Q0043757072697465030C3Q004461726B20426F6E6569746503083Q004461726B7279746503083Q0044656D6F6E69746503073Q004469616D6F6E6403083Q00447572616E69746503073Q00456D6572616C64030B3Q00457468657265616C69746503083Q004576696C2045796503073Q00457965204F7265030A3Q0046696368692Q6C69756D030F3Q0046696368692Q6C69756D6F7269746503073Q004669726569746503073Q0046726F67697465030C3Q0046726F737420466F2Q73696C03083Q0047616C617869746503083Q0047616C6573746F72030A3Q0047617267616E7475616E03043Q00476F6C64030B3Q00476F6C656D20486561727403083Q00477261706869746503053Q004772612Q73030D3Q0047722Q656E204372797374616C03083Q0047756C616269746503133Q004865617274204F66205468652049736C616E6403093Q0048656176656E69746503063Q0049636569746503043Q0049726F6E03043Q004A616465030C3Q004C61706973204C617A756C6903073Q004C6172696D617203073Q004C67617269746503083Q004C69676874697465030F3Q004D6167656E7461204372797374616C03083Q004D61676D6169746503093Q004D616C61636869746503083Q004D6172626C69746503093Q004D6574656F7269746503083Q004D6973747665696E030B3Q004D6F6C74656E66726F7374030A3Q004D2Q6F6E2053746F6E65030B3Q004D6F736173617572736974030B3Q004D757368722Q6F6D69746503073Q004D79746872696C03093Q004E6575726F74697465030C3Q0054696E7920452Q73656E6365030D3Q00536D612Q6C20452Q73656E6365030E3Q004D656469756D20452Q73656E6365030D3Q004C6172676520452Q73656E6365030F3Q004772656174657220452Q73656E636503103Q005375706572696F7220452Q73656E6365030C3Q004570696320452Q73656E636503113Q004C6567656E6461727920452Q73656E636503103Q004D7974686963616C20452Q73656E636503053Q00537572676503063Q0053747269646503053Q00506861736503083Q00566974616C69747903093Q0053776966746E652Q7303093Q00456E647572616E636503053Q005969656C6403043Q004C75636B030A3Q004D696E6520506F776572030C3Q005377696674204D696E696E67030C3Q00412Q7461636B2053702Q6564030F3Q00437269746963616C204368616E6365030F3Q00437269746963616C2044616D61676503093Q004C657468616C69747903083Q00467261637475726503093Q0042616420536D652Q6C03093Q004265727365726B6572030A3Q00466C617420526567656E030B3Q00526164696F61637469766503063Q00536869656C6403053Q0054686F726E030B3Q00546F786963205665696E7303093Q0045585020422Q6F737403093Q00486F6C792048616E64030B3Q00416E67656C20536D69746503123Q0041726368646576696C27732046696E676572030D3Q00496E76696E636962696C69747903113Q0041726368616E67656C277320536D697465030B3Q0042752Q6C2773204675727903083Q004261636B66697265030B3Q004375727365642041757261030E3Q00446576696C27732046696E676572030A3Q004A756D7020422Q6F7374030B3Q004D2Q6F6E204B6E6967687403113Q004E6567617469766520566974616C69747903123Q004E656761746976652053776966746E652Q7303123Q004E6567617469766520456E647572616E6365030C3Q005068616E746F6D2053746570030D3Q005365636F6E64204368616E636503063Q004162736F726203093Q004578706C6F73696F6E03043Q004275726E2Q033Q00496365030A3Q004C69666520537465616C03063Q00506F69736F6E2Q033Q00526F7403043Q00536E6F7703093Q0052616765204D61726B030A3Q0057617264205061746368030B3Q004272696172204E6F746368030A3Q00526F7420537469746368030B3Q004D696E6572205368617264030E3Q004D696E6572205368617264202Q49030D3Q004D696E65722053686172642032030A3Q00426C6173742043686970030B3Q00466C616D6520537061726B030B3Q0046726F737420537065636B030A3Q00447261696E2045646765030B3Q0056656E6F6D204372756D62030A3Q004368692Q6C2044757374030E3Q0046726F737420537065636B202Q49030D3Q004368692Q6C2044757374202Q49026Q000840026Q002640026Q003240026Q002C40026Q003940026Q001840026Q002E40026Q003740026Q003340026Q002Q40026Q001040026Q002240026Q003040026Q001440025Q00804140026Q001C40026Q002840025Q00802Q40026Q005040026Q004940026Q004440025Q00804640026Q004E40026Q003A40026Q003640026Q003C40027Q0040025Q00C05240026Q002A40026Q003840026Q004240025Q00405040025Q00C0574003103Q00412Q7461636B53702Q6564422Q6F7374030B3Q0044616D616765422Q6F7374030E3Q00437269746963616C4368616E6365030E3Q00437269746963616C44616D61676503093Q004C696665537465616C03093Q004D696E65506F77657203093Q004D696E6553702Q6564030D3Q0045787472614D696E6544726F70030E3Q004D696E6544726F704368616E6365030D3Q004D696E6544726F70436F756E7403093Q004C75636B422Q6F7374030C3Q0044617368432Q6F6C646F776E030C3Q004461736844697374616E6365030A3Q0044617368494672616D6503093Q004D6F766553702Q6564030B3Q004865616C7468422Q6F7374030C3Q005374616D696E61422Q6F737403103Q00536869656C6450657263656E74616765030F3Q00466C61744865616C7468526567656E03093Q004963654368616E636503093Q0049636544616D616765030A3Q00536E6F774368616E6365030A3Q00536E6F7744616D616765030F3Q004578706C6F73696F6E4368616E6365030F3Q004578706C6F73696F6E44616D616765030A3Q004275726E4368616E6365030A3Q004275726E44616D616765030C3Q00506F69736F6E4368616E6365030C3Q00506F69736F6E44616D616765030F3Q004265727365726B657244616D616765030E3Q00426164536D652Q6C44616D616765030B3Q0054686F726E44616D61676503103Q00546F7869635665696E7344616D616765030D3Q0053696D706C654C616E7465726E030A3Q00506F7274616C542Q6F6C03163Q004368726973746D61734576656E7443752Q72656E637903043Q004D697363030A3Q0045717569706D656E747303043Q00722Q6F742Q033Q0063747803043Q0074696D65025Q00C0724003093Q00526573657453652Q6C03083Q0053652Q6C4F6E636503123Q0053652Q6C4F6E63654E6F54656C65706F727403153Q0053652Q6C4F6E6365466F72636554656C65706F7274030D3Q0053746172744175746F53652Q6C030C3Q0053746F704175746F53652Q6C03113Q0047657453652Q6C506C617965724461746103143Q0047657453652Q6C46696C7465724F7074696F6E7303133Q004765744F726546696C7465724F7074696F6E7303173Q00476574452Q73656E636546696C7465724F7074696F6E7303143Q0047657452756E6546696C7465724F7074696F6E7303053Q007461626C6503063Q00696E7365727403073Q00436C65616E757003133Q004D6F64756C652076312E30206C6F616465642103063Q004E6F7469667903053Q005469746C65030B3Q0053652Q6C204D6F64756C6503073Q00436F6E74656E74030C3Q0076312E30204C6F616465642103083Q004475726174696F6E03053Q00737061776E006A042Q00120C012Q00013Q0020065Q00022Q00DD3Q0001000200120C2Q0100033Q00206900010001000400122Q000200056Q00010002000100122Q000100063Q00202Q00010001000700062Q0001001B00013Q0004443Q001B000100120C2Q0100063Q00200600010001000700200600010001000800067B0001001B00013Q0004443Q001B000100120C2Q0100063Q00200600010001000700200600010001000800200600010001000900067B0001001B00013Q0004443Q001B000100120C2Q0100063Q00200600010001000700200600010001000A0006F800010021000100010004443Q0021000100120C2Q0100013Q0020060001000100022Q00DD0001000100022Q0051000100013Q000ED2000B0003000100010004443Q0003000100120C2Q0100063Q00200600010001000700067B0001003500013Q0004443Q0035000100120C2Q0100063Q00200600010001000700200600010001000800067B0001003500013Q0004443Q0035000100120C2Q0100063Q00200600010001000700200600010001000800200600010001000900067B0001003500013Q0004443Q0035000100120C2Q0100063Q00200600010001000700200600010001000A0006F800010039000100010004443Q0039000100120C2Q01000C3Q0012000102000D4Q000E2Q01000200012Q00E33Q00013Q00120C2Q01000E3Q00209600010001000F00122Q000300106Q00010003000200122Q0002000E3Q00202Q00020002000F00122Q000400116Q00020004000200122Q0003000E3Q00202Q00030003000F00122Q000500124Q008900030005000200129C0004000E3Q00202Q00040004000F00122Q000600136Q00040006000200122Q0005000E3Q00202Q00050005000F00122Q000700146Q00050007000200202Q00060001001500122Q000700063Q00200600070007000700207F00080007000A4Q00093Q000D00302Q00090016001700302Q00090018001900302Q0009001A001B00302Q0009001C001B00302Q0009001D001700302Q0009001E001B00302Q0009001F001B00302Q00090020001B2Q00E6000A5Q00100E00090021000A4Q000A5Q00102Q00090022000A4Q000A5Q00102Q00090023000A00302Q00090024002500302Q0009002600174Q000A5Q00122Q000B00276Q000C00094Q0011000B0002000D0004443Q006800012Q00BF000A000E000F00068B000B0067000100020004443Q0067000100101C00070028000A0010050007002900094Q000B000B3Q00122Q000C00256Q000D8Q000E5Q00062Q0006007700013Q0004443Q00770001002006000F0006002A0020D9000F000F002B00066700113Q000100012Q005B3Q000E4Q00B1000F001100012Q0009010F00124Q003700135Q00122Q0014002C3Q00122Q0015002D3Q00122Q0016002E6Q00173Q002500302Q0017002F001B00302Q00170030001B00302Q00170031001B00302Q00170032001B00302Q00170033001B00302Q00170034001B00302Q00170035001B00302Q00170036001B00302Q00170037001B00302Q00170038001B00302Q00170039001B00302Q0017003A001B00302Q0017003B001B00302Q0017003C001B00302Q0017003D001B00302Q0017003E001B00302Q0017003F001B00302Q00170040001B00302Q00170041001B00302Q00170042001B00302Q00170043001B00302Q00170044001B00302Q00170045001B00302Q00170046001B00302Q00170047001B00302Q00170048001B00302Q00170049001B00302Q0017004A001B00302Q0017004B001B00302Q0017004C001B00302Q0017004D001B00302Q0017004E001B00302Q0017004F001B00302Q00170050001B00302Q00170051001B00302Q00170052001B00302Q00170053001B00302Q00170054001B00302Q00170055001B00302Q00170056001B00302Q00170057001B00302Q00170058001B00302Q00170059001B00302Q0017005A001B00302Q0017005B001B00302Q0017005C001B00302Q0017005D001B00302Q0017005E001B00302Q0017005F001B00302Q00170060001B00302Q00170061001B00302Q00170062001B00302Q00170063001B00302Q00170064001B00302Q00170065001B00302Q00170066001B00302Q00170067001B00302Q00170068001B00302Q00170069001B00302Q0017006A001B00302Q0017006B001B00302Q0017006C001B00302Q0017006D001B00302Q0017006E001B00302Q0017006F001B00302Q00170070001B00302Q00170071001B00302Q00170072001B00302Q00170073001B00302Q00170074001B00302Q00170075001B00302Q00170076001B00302Q00170077001B00302Q00170078001B00302Q00170079001B0030720017007A001B00303A0017007B001B00302Q0017007C001B00302Q0017007D001B00302Q0017007E001B00302Q0017007F001B00302Q00170080001B00302Q00170081001B00302Q00170082001B00302Q00170083001B00302Q00170084001B00302Q00170085001B00302Q00170086001B00302Q00170087001B00302Q00170088001B00302Q00170089001B00302Q0017008A001B00302Q0017008B001B00302Q0017008C001B00302Q0017008D001B00302Q0017008E001B00302Q0017008F001B00302Q00170090001B4Q00183Q000900302Q00180091001B00302Q00180092001B00302Q00180093001B00302Q00180094001B00302Q00180095001B00302Q00180096001B00302Q00180097001B00302Q00180098001B00302Q00180099001B4Q00193Q002000302Q0019009A001B00302Q0019009B001B00302Q0019009C001B00302Q0019009D001B00302Q0019009E001B00302Q0019009F001B00302Q001900A0001B00302Q001900A1001B00302Q001900A2001B00302Q001900A3001B00302Q001900A4001B00302Q001900A5001B00302Q001900A6001B00302Q001900A7001B00302Q001900A8001B00302Q001900A9001B00302Q001900AA001B00302Q001900AB001B00302Q001900AC001B00302Q001900AD001B00302Q001900AE001B00302Q001900AF001B00302Q001900B0001B00302Q001900B1001B00302Q001900B2001B00302Q001900B3001B00302Q001900B4001B00302Q001900B5001B00302Q001900B6001B00302Q001900B7001B00302Q001900B8001B00302Q001900B9001B00302Q001900BA001B00302Q001900BB001B00302Q001900BC001B00302Q001900BD001B00302Q001900BE001B00302Q001900BF001B00302Q001900C0001B00302Q001900C1001B00302Q001900C2001B00302Q001900C3001B00302Q001900C4001B00302Q001900C5001B00302Q001900C6001B00302Q001900C7001B00302Q001900C8001B00305D001900C9001B00302Q001900CA001B00302Q001900CB001B00302Q001900CC001B00302Q001900CD001B00302Q001900CE001B00302Q001900CF001B00302Q001900D0001B00302Q001900D1001B00302Q001900D2001B003072001900D3001B0030BB001900D4001B00302Q001900D5001B00302Q001900D6001B00302Q001900D7001B4Q001A3Q00174Q001B00036Q001C00023Q00122Q001D00D83Q00122Q001E00D96Q001C000200012Q00E6001D00023Q001200011E002E3Q001200011F00DA4Q0014011D000200012Q00E6001E00023Q001200011F00DB3Q001200012000DC4Q0014011E000200012Q0014011B0003000100101C001A009A001B2Q0048001B00036Q001C00023Q00122Q001D00DD3Q00122Q001E00DE6Q001C000200012Q00E6001D00023Q001200011E000B3Q001200011F00DF4Q0014011D000200012Q00E6001E00023Q001200011F00E03Q001200012000E14Q0014011E000200012Q0014011B0003000100101C001A009B001B2Q0048001B00036Q001C00023Q00122Q001D00E23Q00122Q001E00D96Q001C000200012Q00E6001D00023Q001200011E00E33Q001200011F00E44Q0014011D000200012Q00E6001E00023Q001200011F00DB3Q0012000120002C4Q0014011E000200012Q0014011B0003000100101C001A009C001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E000B6Q001C000200012Q00E6001D00023Q001200011E000B3Q001200011F002C4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000E64Q0014011E000200012Q0014011B0003000100101C001A009D001B2Q0048001B00036Q001C00023Q00122Q001D00E23Q00122Q001E000B6Q001C000200012Q00E6001D00023Q001200011E00E73Q001200011F00DE4Q0014011D000200012Q00E6001E00023Q001200011F000B3Q0012000120002C4Q0014011E000200012Q0014011B0003000100101C001A009E001B2Q0048001B00036Q001C00023Q00122Q001D00E23Q00122Q001E000B6Q001C000200012Q00E6001D00023Q001200011E00E73Q001200011F00DE4Q0014011D000200012Q00E6001E00023Q001200011F000B3Q0012000120002C4Q0014011E000200012Q0014011B0003000100101C001A009F001B2Q0048001B00036Q001C00023Q00122Q001D00D83Q00122Q001E000B6Q001C000200012Q00E6001D00023Q001200011E00E83Q001200011F002C4Q0014011D000200012Q00E6001E00023Q001200011F00DA3Q001200012000E94Q0014011E000200012Q0014011B0003000100101C001A00A0001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E00E46Q001C000200012Q00E6001D00023Q001200011E000B3Q001200011F00E14Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000EA4Q0014011E000200012Q0014011B0003000100101C001A00A1001B2Q0048001B00036Q001C00023Q00122Q001D002E3Q00122Q001E00DE6Q001C000200012Q00E6001D00023Q001200011E00E43Q001200011F00194Q0014011D000200012Q00E6001E00023Q001200011F00E13Q001200012000EB4Q0014011E000200012Q0014011B0003000100101C001A00A2001B2Q0048001B00036Q001C00023Q00122Q001D00E23Q00122Q001E00E86Q001C000200012Q00E6001D00023Q001200011E00E83Q001200011F00DC4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000EC4Q0014011E000200012Q0014011B0003000100101C001A00A3001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E00DA6Q001C000200012Q00E6001D00023Q001200011E00DE3Q001200011F00194Q0014011D000200012Q00E6001E00023Q001200011F00DC3Q001200012000EC4Q0014011E000200012Q0014011B0003000100101C001A00A4001B2Q0048001B00036Q001C00023Q00122Q001D00DD3Q00122Q001E00DE6Q001C000200012Q00E6001D00023Q001200011E00DE3Q001200011F00DC4Q0014011D000200012Q00E6001E00023Q001200011F00DC3Q001200012000EC4Q0014011E000200012Q0014011B0003000100101C001A00A5001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E00DE6Q001C000200012Q00E6001D00023Q001200011E00DE3Q001200011F00DC4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000EC4Q0014011E000200012Q0014011B0003000100101C001A00A6001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E00DE6Q001C000200012Q00E6001D00023Q001200011E00E83Q001200011F00DF4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000E64Q0014011E000200012Q0014011B0003000100101C001A00A7001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E002C6Q001C000200012Q00E6001D00023Q001200011E00DE3Q001200011F00ED4Q0014011D000200012Q00E6001E00023Q001200011F00DC3Q001200012000EE4Q0014011E000200012Q0014011B0003000100101C001A00A8001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E00E86Q001C000200012Q00E6001D00023Q001200011E00E83Q001200011F002C4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000194Q0014011E000200012Q0014011B0003000100101C001A00A9001B2Q0048001B00036Q001C00023Q00122Q001D00E83Q00122Q001E00EF6Q001C000200012Q00E6001D00023Q001200011E00DC3Q001200011F00EC4Q0014011D000200012Q00E6001E00023Q001200011F00E63Q001200012000EE4Q0014011E000200012Q0014011B0003000100101C001A00AA001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E000B6Q001C000200012Q00E6001D00023Q001200011E000B3Q001200011F002C4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000E64Q0014011E000200012Q0014011B0003000100101C001A00AB001B2Q0048001B00016Q001C00023Q00122Q001D00E53Q00122Q001E00DE6Q001C000200012Q0014011B0001000100101C001A00AC001B2Q0048001B00036Q001C00023Q00122Q001D00DD3Q00122Q001E00DB6Q001C000200012Q00E6001D00023Q001200011E00D93Q001200011F00F04Q0014011D000200012Q00E6001E00023Q001200011F00DA3Q001200012000F14Q0014011E000200012Q0014011B0003000100101C001A00AD001B2Q0048001B00036Q001C00023Q00122Q001D00F23Q00122Q001E000B6Q001C000200012Q00E6001D00023Q001200011E000B3Q001200011F00DC4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000E64Q0014011E000200012Q0014011B0003000100101C001A00AE001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E00DE6Q001C000200012Q00E6001D00023Q001200011E000B3Q001200011F00DC4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000EC4Q0014011E000200012Q0014011B0003000100101C001A00AF001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E000B6Q001C000200012Q00E6001D00023Q001200011E000B3Q001200011F002C4Q0014011D000200012Q00E6001E00023Q001200011F002C3Q001200012000E64Q0014011E000200012Q0014011B0003000100101C001A00B0001B2Q0048001B00036Q001C00023Q00122Q001D002E3Q00122Q001E002C6Q001C000200012Q00E6001D00023Q001200011E002C3Q001200011F00E64Q0014011D000200012Q00E6001E00023Q001200011F00E63Q001200012000EB4Q0014011E000200012Q0014011B0003000100101C001A00C2001B2Q0048001B00036Q001C00023Q00122Q001D00DE3Q00122Q001E00DC6Q001C000200012Q00E6001D00023Q001200011E002C3Q001200011F00EB4Q0014011D000200012Q00E6001E00023Q001200011F00ED3Q001200012000F34Q0014011E000200012Q0014011B0003000100101C001A00C3001B2Q0048001B00036Q001C00023Q00122Q001D000B3Q00122Q001E002C6Q001C000200012Q00E6001D00023Q001200011E00DE3Q001200011F00EC4Q0014011D000200012Q00E6001E00023Q001200011F00E63Q001200012000EE4Q0014011E000200012Q0014011B0003000100101C001A00C4001B2Q0048001B00036Q001C00023Q00122Q001D00E23Q00122Q001E00D96Q001C000200012Q00E6001D00023Q001200011E00F43Q001200011F00F54Q0014011D000200012Q00E6001E00023Q001200011F00F53Q001200012000F64Q0014011E000200012Q0014011B0003000100101C001A00C5001B2Q0048001B00036Q001C00023Q00122Q001D00DC3Q00122Q001E00E66Q001C000200012Q00E6001D00023Q001200011E00E63Q001200011F00F74Q0014011D000200012Q00E6001E00023Q001200011F00EE3Q001200012000F84Q0014011E000200012Q0014011B0003000100101C001A00C6001B2Q0048001B00036Q001C00023Q00122Q001D00E23Q00122Q001E00E76Q001C000200012Q00E6001D00023Q001200011E00E73Q001200011F00F44Q0014011D000200012Q00E6001E00023Q001200011F00F43Q0012000120002C4Q0014011E000200012Q0014011B0003000100101C001A00C7001B2Q0048001B00036Q001C00023Q00122Q001D00E53Q00122Q001E00DE6Q001C000200012Q00E6001D00023Q001200011E00DE3Q001200011F00DC4Q0014011D000200012Q00E6001E00023Q001200011F00DC3Q001200012000E64Q0014011E000200012Q0014011B0003000100101C001A00C8001B2Q00E6001B3Q00152Q00E6001C00013Q001200011D00F94Q0014011C0001000100101C001B00F9001C2Q00E6001C00013Q001200011D00FA4Q0014011C0001000100101C001B00FA001C2Q00E6001C00013Q001200011D00FB4Q0014011C0001000100101C001B00FB001C2Q00E6001C00013Q001200011D00FC4Q0014011C0001000100101C001B00FC001C2Q00E6001C00013Q001200011D00FD4Q0014011C0001000100101C001B00FD001C2Q00E6001C00013Q001200011D00FE4Q0014011C0001000100101C001B00FE001C2Q00E6001C00013Q001200011D00FF4Q0014011C0001000100101C001B00FF001C2Q00E6001C00023Q001200011D002Q012Q001200011E0002013Q0014011C0002000100101C001B2Q00011C001200011C0003013Q00E6001D00013Q001200011E0003013Q0014011D000100012Q00BF001B001C001D001200011C0004013Q00E6001D00013Q001200011E0004013Q0014011D000100012Q00BF001B001C001D001200011C0005013Q00E6001D00013Q001200011E0005013Q0014011D000100012Q00BF001B001C001D001200011C0006013Q00E6001D00013Q001200011E0006013Q0014011D000100012Q00BF001B001C001D001200011C0007013Q00E6001D00013Q001200011E0007013Q0014011D000100012Q00BF001B001C001D001200011C0008013Q00E6001D00013Q001200011E0008013Q0014011D000100012Q00BF001B001C001D001200011C0009013Q00E6001D00013Q001200011E0009013Q0014011D000100012Q00BF001B001C001D001200011C000A013Q00E6001D00013Q001200011E000A013Q0014011D000100012Q00BF001B001C001D001200011C000B013Q00E6001D00013Q001200011E000B013Q0014011D000100012Q00BF001B001C001D2Q00E6001C00023Q001200011D000C012Q001200011E000D013Q0014011C0002000100101C001B00C4001C2Q00E6001C00023Q001200011D000E012Q001200011E000F013Q0014011C0002000100101C001B00C8001C2Q00E6001C00023Q001200011D0010012Q001200011E0011013Q0014011C0002000100101C001B00C2001C2Q00E6001C00023Q001200011D0012012Q001200011E0013013Q0014011C0002000100101C001B00C3001C2Q00E6001C00023Q001200011D0014012Q001200011E0015013Q0014011C0002000100101C001B00C6001C2Q00E6001C00013Q001200011D0016013Q0014011C0001000100101C001B00AA001C001200011C0017013Q00E6001D00013Q001200011E0017013Q0014011D000100012Q00BF001B001C001D001200011C0018013Q00E6001D00013Q001200011E0018013Q0014011D000100012Q00BF001B001C001D001200011C0019013Q00E6001D00013Q001200011E0019013Q0014011D000100012Q00BF001B001C001D2Q0040001C3Q000500122Q001D001A015Q001E00016Q001C001D001E00122Q001D001B015Q001E00016Q001C001D001E00122Q001D001C015Q001E00016Q001C001D001E001200011D001D013Q0013011E00016Q001C001D001E00122Q001D001E015Q001E00016Q001C001D001E4Q001D5Q00122Q001E00253Q000667001F0001000100032Q005B3Q001D4Q005B3Q001E4Q005B3Q00063Q000285002000023Q00066700210003000100022Q005B3Q000A4Q005B3Q00203Q00066700220004000100022Q005B3Q000A4Q005B3Q00203Q00066700230005000100022Q005B3Q000A4Q005B3Q00203Q000285002400063Q00066700250007000100012Q005B3Q00083Q000285002600083Q00066700270009000100012Q005B3Q00263Q0002850028000A4Q000401293Q000300122Q002A001F015Q002B002B6Q0029002A002B00122Q002A0020015Q002B002B6Q0029002A002B00122Q002A0021012Q00122Q002B00256Q0029002A002B2Q0009012A002B3Q001200012C00253Q000667002D000B000100052Q005B3Q002A4Q005B3Q00024Q005B3Q00294Q005B3Q002B4Q005B3Q002C3Q000667002E000C000100032Q005B3Q002D4Q005B3Q00024Q005B3Q00293Q000667002F000D000100032Q005B3Q002B4Q005B3Q002C4Q005B3Q00243Q0006670030000E000100012Q005B3Q00063Q0006670031000F000100012Q005B3Q00023Q00066700320010000100012Q005B3Q00053Q00066700330011000100012Q005B3Q00063Q000285003400123Q00066700350013000100022Q005B3Q00334Q005B3Q00343Q00066700360014000100012Q005B3Q00353Q00066700370015000100012Q005B3Q00353Q00066700380016000100022Q005B3Q00024Q005B3Q00064Q0009013900393Q001200013A00253Q001200013B0022012Q000667003C0017000100062Q005B3Q00394Q005B3Q003A4Q005B3Q003B4Q005B3Q00364Q005B3Q00374Q005B3Q00383Q000667003D0018000100012Q005B3Q00063Q000667003E0019000100012Q005B3Q00053Q000285003F001A3Q0002850040001B3Q0006670041001C0001000A2Q005B3Q003C4Q005B3Q00244Q005B3Q003F4Q005B3Q00174Q005B3Q00214Q005B3Q000A4Q005B3Q00184Q005B3Q00224Q005B3Q001B4Q005B3Q00233Q0006670042001D000100022Q005B3Q00054Q005B3Q00063Q0002850043001E3Q0006670044001F000100022Q005B3Q000F4Q005B3Q00053Q00066700450020000100022Q005B3Q000F4Q005B3Q00153Q00066700460021000100012Q005B3Q000F3Q00066700470022000100072Q005B3Q00134Q005B3Q00114Q005B3Q00124Q005B3Q00424Q005B3Q00434Q005B3Q00104Q005B3Q00463Q000667004800230001000D2Q005B3Q00134Q005B3Q00474Q005B3Q00424Q005B3Q00434Q005B3Q00244Q005B3Q00444Q005B3Q00454Q005B3Q00124Q005B3Q00034Q005B3Q00114Q005B3Q00164Q005B3Q00144Q005B3Q00103Q00066700490024000100042Q005B3Q002E4Q005B3Q00244Q005B3Q002B4Q005B3Q002C3Q000667004A0025000100042Q005B3Q00424Q005B3Q00244Q005B3Q00044Q005B3Q00063Q000667004B0026000100142Q005B3Q000D4Q005B3Q00304Q005B3Q00414Q005B3Q000C4Q005B3Q00254Q005B3Q00244Q005B3Q00314Q005B3Q00324Q005B3Q00424Q005B3Q00434Q005B3Q000E4Q005B3Q002F4Q005B3Q00494Q005B3Q000A4Q005B3Q003E4Q005B3Q004A4Q005B3Q00284Q005B3Q003D4Q005B3Q00274Q005B3Q00023Q000667004C0027000100072Q005B3Q000B4Q005B3Q000A4Q005B3Q000D4Q005B3Q000C4Q005B3Q00244Q005B3Q004B4Q005B3Q00303Q000667004D0028000100022Q005B3Q000A4Q005B3Q000B3Q001200014E0023012Q000667004F0029000100062Q005B3Q000A4Q005B3Q000D4Q005B3Q000E4Q005B3Q000C4Q005B3Q00094Q005B3Q00244Q00BF0007004E004F001200014E0024013Q00BF0007004E004B001200014E0025012Q000667004F002A000100012Q005B3Q004B4Q00BF0007004E004F001200014E0026012Q000667004F002B000100012Q005B3Q004B4Q00C90007004E004F00122Q004E0027015Q0007004E004C00122Q004E0028015Q0007004E004D00122Q004E0029015Q0007004E003C00122Q004E002A012Q000667004F002C000100022Q005B3Q00174Q005B3Q00194Q00BF0007004E004F001200014E002B013Q00BF0007004E001F001200014E002C012Q000667004F002D000100012Q005B3Q00184Q00BF0007004E004F001200014E002D012Q000667004F002E000100012Q005B3Q00194Q00BF0007004E004F000667004E002F000100042Q005B3Q004D4Q005B3Q00474Q005B3Q002A4Q005B3Q00243Q0012B4004F002E012Q00122Q0050002F015Q004F004F005000122Q00500030015Q0050000700504Q0051004E6Q004F005100014Q004F00243Q00122Q00500031015Q004F0002000100120001510032013Q004D004F000800514Q00513Q000300122Q00520033012Q00122Q00530034015Q00510052005300122Q00520035012Q00122Q00530036015Q00510052005300122Q00520037012Q00122Q005300F24Q00BF0051005200532Q00B1004F0051000100120C014F00033Q00120001500038013Q0082004F004F005000066700500030000100072Q005B3Q000A4Q005B3Q004C4Q005B3Q004D4Q005B3Q001F4Q005B3Q00174Q005B3Q00184Q005B3Q00194Q000E014F000200012Q00E33Q00013Q00318Q00034Q00FD8Q00ED8Q00E33Q00017Q00193Q0003043Q007469636B028Q00026Q00244003053Q007063612Q6C030C3Q005549477269644C61796F75742Q01030C3Q0055494C6973744C61796F757403093Q00554950612Q64696E6703173Q005549417370656374526174696F436F6E73747261696E7403073Q0055495363616C6503083Q0055495374726F6B6503083Q005549436F726E657203053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D652Q033Q00737562026Q0014C003053Q00204C69737403093Q00436C612Q734E616D6503053Q007461626C6503063Q00696E7365727403043Q00736F727403053Q007072696E7403203Q005B53652Q6C5D2047657444796E616D69634F72654C6973743A20466F756E6420030C3Q0020756E69717565206F72657301573Q00120C2Q0100014Q00DD0001000100020006F83Q000E000100010004443Q000E00012Q000B00026Q006F000200023Q000ED20002000E000100020004443Q000E00012Q000B000200014Q005100020001000200266C0002000E000100030004443Q000E00012Q000B00026Q00BD000200024Q00E600026Q00E600035Q00120C010400043Q00066700053Q000100012Q000B3Q00024Q001100040002000500067B0004001800013Q0004443Q001800010006F80005001A000100010004443Q001A00012Q000B00066Q00BD000600024Q00E600063Q00070030AA00060005000600302Q00060007000600302Q00060008000600302Q00060009000600302Q0006000A000600302Q0006000B000600302Q0006000C000600122Q0007000D3Q00202Q00080005000E4Q000800096Q00073Q000900044Q00470001002006000C000B000F0020D9000C000C0010001200010E00114Q0089000C000E0002002668000C0047000100120004443Q0047000100120C010C000D3Q0020D9000D000B000E2Q0043000D000E4Q0077000C3Q000E0004443Q0045000100200600110010000F2Q00820011000600110006F800110045000100010004443Q004500010020060011001000132Q00820011000600110006F800110045000100010004443Q0045000100200600110010000F2Q00820011000300110006F800110045000100010004443Q0045000100200600110010000F0020EF00030011000600122Q001100143Q00202Q0011001100154Q001200023Q00202Q00130010000F4Q00110013000100068B000C0032000100020004443Q0032000100068B00070027000100020004443Q0027000100120C010700143Q0020520007000700164Q000800026Q0007000200014Q00028Q000100013Q00122Q000700173Q00122Q000800186Q000900023Q00122Q000A00196Q00080008000A4Q0007000200014Q000200028Q00013Q00013Q00073Q0003093Q00506C6179657247756903043Q004D656E7503053Q004672616D6503053Q004D656E757303053Q00496E64657803053Q00506167657303043Q004F726573000B4Q009E7Q00206Q000100206Q000200206Q000300206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00033Q0003043Q007479706503053Q007461626C6503053Q00706169727302143Q00120C010200014Q005B00036Q00D500020002000200267400020007000100020004443Q000700012Q00FD00026Q00BD000200023Q00120C010200034Q005B00036Q00110002000200040004443Q000F00010006980006000F000100010004443Q000F00012Q00FD000700014Q00BD000700023Q00068B0002000B000100020004443Q000B00012Q00FD00026Q00BD000200024Q00E33Q00017Q00033Q0003083Q0053652Q6C4F726573030D3Q004F726546696C7465724C697374028Q0001174Q000B00015Q0020060001000100010006F800010006000100010004443Q000600012Q00FD00016Q00BD000100024Q000B00015Q0020060001000100020006F80001000B000100010004443Q000B00012Q00E600016Q006F000200013Q00266800020010000100030004443Q001000012Q00FD000200014Q00BD000200024Q000B000200014Q00AB000300016Q00048Q0002000400024Q000200026Q000200028Q00017Q00033Q00030C3Q0053652Q6C452Q73656E63657303113Q00452Q73656E636546696C7465724C697374028Q0001174Q000B00015Q0020060001000100010006F800010006000100010004443Q000600012Q00FD00016Q00BD000100024Q000B00015Q0020060001000100020006F80001000B000100010004443Q000B00012Q00E600016Q006F000200013Q00266800020010000100030004443Q001000012Q00FD000200014Q00BD000200024Q000B000200014Q00AB000300016Q00048Q0002000400024Q000200026Q000200028Q00017Q00133Q0003093Q0053652Q6C52756E657303143Q0052756E655175616C6974795468726573686F6C64028Q0003113Q005374726963745175616C6974794D6F64652Q0103063Q0069706169727303053Q0076616C756503093Q0044656275674D6F646503053Q007072696E7403063Q00737472696E6703063Q00666F726D617403303Q005B53652Q6C2044656275675D204B2Q45502028537472696374293A20412Q4C20747261697473203E3D20252E30662Q25026Q005940033A3Q005B53652Q6C2044656275675D204B2Q45503A202573206861732076616C756520252E31662Q2520287468726573686F6C643A20252E30662Q252903043Q006E616D6503013Q003F030E3Q0052756E6546696C7465724C69737403053Q007461626C6503063Q00696E7365727402884Q000B00025Q0020060002000200010006F800020006000100010004443Q000600012Q00FD00026Q00BD000200024Q000B00025Q0020060002000200020006F80002000B000100010004443Q000B0001001200010200034Q000B00035Q00200600030003000400267400030010000100050004443Q001000012Q006200036Q00FD000300013Q000ED200030055000100020004443Q0055000100067B3Q005500013Q0004443Q005500012Q006F00045Q000ED200030055000100040004443Q0055000100067B0003003800013Q0004443Q003800012Q00FD000400013Q00120C010500064Q005B00066Q00110005000200070004443Q00260001002006000A0009000700067B000A002400013Q0004443Q00240001000678000A0026000100020004443Q002600012Q00FD00045Q0004443Q0028000100068B0005001F000100020004443Q001F000100067B0004005500013Q0004443Q005500012Q000B00055Q00200600050005000800067B0005003500013Q0004443Q0035000100120C010500093Q0012460006000A3Q00202Q00060006000B00122Q0007000C3Q00202Q00080002000D4Q000600086Q00053Q00012Q00FD00056Q00BD000500023Q0004443Q0055000100120C010400064Q005B00056Q00110004000200060004443Q0053000100200600090008000700067B0009005300013Q0004443Q0053000100063200020053000100090004443Q005300012Q000B000A5Q002006000A000A000800067B000A005100013Q0004443Q0051000100120C010A00093Q0012B3000B000A3Q00202Q000B000B000B00122Q000C000E3Q00202Q000D0008000F00062Q000D004D000100010004443Q004D0001001200010D00103Q0020E8000E0009000D0020E8000F0002000D2Q00D1000B000F4Q006A000A3Q00012Q00FD000A6Q00BD000A00023Q00068B0004003C000100020004443Q003C00012Q000B00045Q0020060004000400110006F80004005A000100010004443Q005A00012Q00E600046Q006F000500043Q0026680005005F000100030004443Q005F00012Q00FD000500014Q00BD000500024Q00E600055Q00120C010600063Q0006A80007006400013Q0004443Q006400012Q00E600076Q00110006000200080004443Q006E0001002006000B000A000F00067B000B006E00013Q0004443Q006E000100120C010B00123Q002006000B000B00132Q005B000C00053Q002006000D000A000F2Q00B1000B000D000100068B00060066000100020004443Q0066000100067B0001007700013Q0004443Q0077000100120C010600123Q0020060006000600132Q005B000700054Q005B000800014Q00B100060008000100120C010600064Q005B000700054Q00110006000200080004443Q008300012Q000B000B00014Q005B000C00044Q005B000D000A4Q0089000B000D000200067B000B008300013Q0004443Q008300012Q00FD000B00014Q00BD000B00023Q00068B0006007B000100020004443Q007B00012Q00FD00066Q00BD000600024Q00E33Q00017Q00053Q0003053Q007072696E7403073Q005B53652Q6C5D2003023Q005F4703053Q00466F7267652Q033Q004C6F6701163Q00120F2Q0100013Q00122Q000200026Q00038Q0002000200034Q00010002000100122Q000100033Q00202Q00010001000400062Q0001001500013Q0004443Q0015000100120C2Q0100033Q00200600010001000400200600010001000500067B0001001500013Q0004443Q0015000100120C2Q0100033Q0020AE00010001000400202Q00010001000500122Q000200026Q00038Q0002000200034Q0001000200012Q00E33Q00017Q00013Q0003053Q007063612Q6C03083Q00120C010300013Q00066700043Q000100042Q000B8Q005B8Q005B3Q00014Q005B3Q00024Q000E0103000200012Q00E33Q00013Q00013Q00053Q0003063Q004E6F7469667903053Q005469746C6503073Q00436F6E74656E7403083Q004475726174696F6E027Q0040000E4Q00637Q00206Q00014Q00023Q00034Q000300013Q00102Q0002000200034Q000300023Q00102Q0002000300034Q000300033Q00062Q0003000B000100010004443Q000B0001001200010300053Q00101C0002000400032Q00B13Q000200012Q00E33Q00017Q00073Q0003043Q007479706503053Q007461626C6503063Q0072617767657403063Q006E756D626572028Q0003073Q00622Q6F6C65616E0100021E3Q00120C010200014Q005B00036Q00D500020002000200267400020007000100020004443Q000700012Q00FD00026Q00BD000200023Q00120C010200034Q008C00038Q000400016Q00020004000200122Q000300016Q000400026Q00030002000200262Q00030013000100040004443Q001300010020D63Q000100052Q00FD000300014Q00BD000300023Q00120C010300014Q005B000400024Q00D50003000200020026680003001B000100060004443Q001B00010020D63Q000100072Q00FD000300014Q00BD000300024Q00FD00036Q00BD000300024Q00E33Q00017Q00043Q0003043Q007479706503053Q007461626C65030C3Q0044617368432Q6F6C646F776E03073Q0044617368696E6701183Q00120C2Q0100014Q005B00026Q00D500010002000200267400010007000100020004443Q000700012Q00FD00016Q00BD000100024Q00FD00016Q007100028Q00035Q00122Q000400036Q00020004000200062Q0002000F00013Q0004443Q000F00012Q00FD000100014Q000B00026Q005B00035Q001200010400044Q008900020004000200067B0002001600013Q0004443Q001600012Q00FD000100014Q00BD000100024Q00E33Q00017Q00083Q0003043Q007479706503063Q00737472696E6703053Q006C6F776572030A3Q006E6F6D6F76656D656E74030F3Q0064697361626C656261636B7061636B03063Q006E6F64617368030B3Q0064697361626C6564617368030E3Q006E6F64617368632Q6F6C646F776E01173Q00120C2Q0100014Q005B00026Q00D500010002000200267400010007000100020004443Q000700012Q00FD00016Q00BD000100023Q0020D900013Q00032Q00D500010002000200267400010014000100040004443Q0014000100267400010014000100050004443Q0014000100267400010014000100060004443Q0014000100267400010014000100070004443Q0014000100267400010014000100080004443Q001400012Q006200026Q00FD000200014Q00BD000200024Q00E33Q00017Q00053Q0003093Q00436F2Q6E6563746564030E3Q0046696E6446697273744368696C64030E3Q004469616C6F67756552656D6F7465030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637400194Q000B7Q00067B3Q000800013Q0004443Q000800012Q000B7Q0020065Q000100067B3Q000800013Q0004443Q000800012Q00E33Q00014Q000B3Q00013Q002018014Q000200122Q000200036Q000300018Q0003000200064Q0010000100010004443Q001000012Q00E33Q00013Q00200600013Q00040020D900010001000500066700033Q000100032Q000B3Q00024Q000B3Q00034Q000B3Q00044Q00890001000300022Q00ED00016Q00E33Q00013Q00013Q00053Q0003043Q00722Q6F742Q033Q0063747803043Q0074696D6503043Q007469636B030F3Q0053652Q6C436F6E6669726D4D697363020F4Q00F500025Q00102Q000200016Q00025Q00102Q0002000200014Q00025Q00122Q000300046Q00030001000200102Q00020003000300264Q000E000100050004443Q000E00012Q00ED000100013Q00120C010200044Q00DD0002000100022Q00ED000200024Q00E33Q00017Q000D3Q00030E3Q0046696E6446697273744368696C64030E3Q004469616C6F67756552656D6F746503043Q007469636B027Q004003043Q00722Q6F7403043Q0074696D652Q033Q00637478030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637403043Q007461736B03043Q0077616974029A5Q99A93F030A3Q00446973636F2Q6E656374024E4Q000C00028Q0002000100014Q000200013Q00202Q00020002000100122Q000400026Q000500016Q00020005000200062Q0002000B00013Q0004443Q000B00010006F83Q000E000100010004443Q000E00012Q00FD00036Q0009010400044Q0001000300033Q00120C010300034Q00DD0003000100020006A800040013000100010004443Q00130001001200010400044Q000B000500023Q0020060005000500050006980005002200013Q0004443Q0022000100120C010500034Q003D0005000100024Q000600023Q00202Q0006000600064Q00050005000600062Q00050022000100040004443Q002200012Q00FD000500014Q000B000600023Q0020060006000600072Q0001000500034Q00FD00056Q0009010600073Q0020060008000200080020D9000800080009000667000A3Q000100032Q005B8Q005B3Q00054Q005B3Q00064Q00890008000A00022Q005B000700083Q0006F800050046000100010004443Q0046000100120C010800034Q00DD0008000100022Q005100080008000300067800080046000100040004443Q0046000100120C0108000A3Q0020D300080008000B00122Q0009000C6Q0008000200014Q000800023Q00202Q00080008000500062Q0008002C00013Q0004443Q002C000100120C010800034Q003D0008000100024Q000900023Q00202Q0009000900064Q00080008000900062Q0008002C000100040004443Q002C00012Q00FD000500014Q000B000800023Q0020060006000800070004443Q002C000100067B0007004A00013Q0004443Q004A00010020D900080007000D2Q000E0108000200012Q005B000800054Q005B000900064Q0001000800034Q00E33Q00013Q00017Q0002074Q000B00025Q0006983Q0006000100020004443Q000600012Q00FD000200014Q00ED000200014Q00ED000100024Q00E33Q00017Q00053Q0003043Q007469636B025Q0020AC4003303Q0052657573696E67206361636865642053652Q6C436F6E6669726D20636F6E7465787420286E6F2074656C65706F727429030D3Q004469616C6F6775654576656E7403053Q007063612Q6C011C4Q000B00015Q0006F800010005000100010004443Q000500012Q00FD00016Q00BD000100023Q00120C2Q0100014Q00DD0001000100022Q000B000200014Q0051000100010002000ED20002000D000100010004443Q000D00012Q00FD00016Q00BD000100024Q000B000100023Q001200010200034Q000E2Q010002000100067B3Q001900013Q0004443Q0019000100200600013Q000400067B0001001900013Q0004443Q0019000100120C2Q0100053Q00066700023Q000100012Q005B8Q000E2Q01000200012Q00FD000100014Q00BD000100024Q00E33Q00013Q00013Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00107Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00073Q00030E3Q0046696E6446697273744368696C6403093Q00506C61796572477569030A3Q004469616C6F6775655549030F3Q004469616C6F67756548616E646C65722Q033Q00497341030B3Q004C6F63616C53637269707403053Q007063612Q6C011D4Q008E00015Q00202Q00010001000100122Q000300026Q00010003000200062Q00010007000100010004443Q000700012Q00E33Q00013Q0020D9000200010001001200010400034Q00890002000400020006F80002000D000100010004443Q000D00012Q00E33Q00013Q0020D9000300020001001200010500044Q008900030005000200067B0003001C00013Q0004443Q001C00010020D9000400030005001200010600064Q008900040006000200067B0004001C00013Q0004443Q001C000100120C010400073Q00066700053Q000100022Q005B3Q00034Q005B8Q000E0104000200012Q00E33Q00013Q00013Q00013Q0003083Q0044697361626C6564000A4Q000B8Q000B000100013Q00067B0001000700013Q0004443Q000700012Q00FD000100013Q0006F800010008000100010004443Q000800012Q00FD00015Q00101C3Q000100012Q00E33Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q00536572766963657303103Q0050726F78696D69747953657276696365030F3Q004469616C6F6775655365727669636503023Q00524603023Q005245030D3Q00466F7263654469616C6F67756503083Q004469616C6F677565030A3Q0052756E436F2Q6D616E64030D3Q004469616C6F6775654576656E7400474Q00567Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004443Q000900010020D900013Q0001001200010300034Q00890001000300020006950002000E000100010004443Q000E00010020D9000200010001001200010400044Q008900020004000200069500030013000100020004443Q001300010020D9000300020001001200010500054Q008900030005000200069500040018000100030004443Q001800010020D9000400030001001200010600064Q00890004000600020006950005001D000100030004443Q001D00010020D9000500030001001200010700074Q008900050007000200069500060022000100040004443Q002200010020D9000600040001001200010800084Q008900060008000200069500070027000100050004443Q002700010020D9000700050001001200010900084Q00890007000900020006950008002C000100050004443Q002C00010020D9000800050001001200010A00094Q00890008000A00022Q00E600093Q0004000695000A0032000100060004443Q003200010020D9000A00060001001200010C000A4Q0089000A000C000200101C0009000A000A000695000A0038000100060004443Q003800010020D9000A00060001001200010C000B4Q0089000A000C000200101C0009000B000A000695000A003E000100070004443Q003E00010020D9000A00070001001200010C000C4Q0089000A000C000200101C0009000C000A000695000A0044000100080004443Q004400010020D9000A00080001001200010C000D4Q0089000A000C000200101C0009000D000A2Q00BD000900024Q00E33Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403093Q0050726F78696D697479030A3Q0047722Q65647920436579000B4Q00567Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004443Q000900010020D900013Q0001001200010300034Q00890001000300022Q00BD000100024Q00E33Q00017Q00023Q0003063Q0055736572496403083Q00746F6E756D62657201164Q000B00015Q00067B0001000500013Q0004443Q000500012Q000B00015Q0020060001000100010006F800010009000100010004443Q000900012Q00FD00026Q00BD000200023Q0006983Q000D000100010004443Q000D00012Q00FD000200014Q00BD000200023Q00120C010200024Q005B00036Q00D500020002000200063100020013000100010004443Q001300012Q006200036Q00FD000300014Q00BD000300024Q00E33Q00017Q00083Q0003043Q007479706503053Q007461626C6503063Q0072617767657403043Q004D697363030A3Q0045717569706D656E747303053Q00706169727303063Q00737472696E6703063Q006E756D62657201333Q00120C2Q0100014Q005B00026Q00D500010002000200267400010007000100020004443Q000700012Q00FD00016Q00BD000100023Q00120C2Q0100013Q001247000200036Q00035Q00122Q000400046Q000200046Q00013Q000200262Q00010017000100020004443Q0017000100120C2Q0100013Q0012CA000200036Q00035Q00122Q000400056Q000200046Q00013Q000200262Q00010019000100020004443Q001900012Q00FD000100014Q00BD000100023Q00120C2Q0100064Q005B00026Q00110001000200030004443Q002E000100120C010600014Q005B000700044Q00D50006000200020026680006002E000100070004443Q002E000100120C010600014Q005B000700054Q00D50006000200020026740006002C000100080004443Q002C000100120C010600014Q005B000700054Q00D50006000200020026680006002E000100020004443Q002E00012Q00FD000600014Q00BD000600023Q00068B0001001D000100020004443Q001D00012Q00FD00016Q00BD000100024Q00E33Q00017Q00083Q0003053Q00706169727303043Q007479706503053Q007461626C6503063Q0072617767657403043Q004461746103093Q00496E76656E746F727903043Q005461677303063Q0055736572496401473Q00120C010200014Q005B00036Q00110002000200040004443Q0043000100120C010700024Q005B000800064Q00D500070002000200266800070043000100030004443Q0043000100120C010700044Q0007010800063Q00122Q000900056Q00070009000200122Q000800026Q000900076Q00080002000200262Q00080037000100030004443Q0037000100120C010800044Q0007010900073Q00122Q000A00066Q0008000A000200122Q000900026Q000A00086Q00090002000200262Q00090037000100030004443Q0037000100120C010900044Q0007010A00063Q00122Q000B00076Q0009000B000200122Q000A00026Q000B00096Q000A0002000200262Q000A002D000100030004443Q002D00012Q000B000A5Q00121A000B00046Q000C00093Q00122Q000D00086Q000B000D6Q000A3Q000200062Q000A002D00013Q0004443Q002D00012Q00BD000700023Q0006F800090037000100010004443Q003700010006F800010037000100010004443Q003700012Q000B000A00014Q005B000B00084Q00D5000A0002000200067B000A003700013Q0004443Q003700012Q005B000100073Q00120C010800044Q005B000900063Q001200010A00064Q00890008000A00020006F800010043000100010004443Q004300012Q000B000900014Q005B000A00084Q00D500090002000200067B0009004300013Q0004443Q004300012Q005B000100063Q00068B00020004000100020004443Q000400012Q00BD000100024Q00E33Q00017Q00053Q0003043Q007479706503053Q00676574676303083Q0066756E6374696F6E03053Q007063612Q6C03053Q007461626C6500193Q00120C012Q00013Q00120C2Q0100024Q00D53Q000200020026743Q0007000100030004443Q000700012Q0009017Q00BD3Q00023Q00120C012Q00043Q00120C2Q0100024Q00FD000200014Q00BA3Q0002000100067B3Q001200013Q0004443Q0012000100120C010200014Q005B000300014Q00D500020002000200267400020014000100050004443Q001400012Q0009010200024Q00BD000200024Q000B00026Q005B000300014Q0087000200034Q005300026Q00E33Q00017Q00063Q0003043Q007479706503053Q00646562756703053Q007461626C65030B3Q00676574726567697374727903083Q0066756E6374696F6E03053Q007063612Q6C001F3Q00120C012Q00013Q00120C2Q0100024Q00D53Q000200020026683Q000B000100030004443Q000B000100120C012Q00013Q00120C2Q0100023Q0020060001000100042Q00D53Q000200020026743Q000D000100050004443Q000D00012Q0009017Q00BD3Q00023Q00120C012Q00063Q00120C2Q0100023Q0020060001000100042Q00113Q0002000100067B3Q001800013Q0004443Q0018000100120C010200014Q005B000300014Q00D50002000200020026740002001A000100030004443Q001A00012Q0009010200024Q00BD000200024Q000B00026Q005B000300014Q0087000200034Q005300026Q00E33Q00017Q00103Q00030E3Q0046696E6446697273744368696C64030D3Q005265706C696361436C69656E7403053Q007063612Q6C03073Q007265717569726503043Q007479706503053Q007461626C6503063Q0055736572496403083Q005265706C6963617303093Q005F7265706C6963617303083Q007265706C6963617303053Q00706169727303063Q0072617767657403043Q005461677303043Q004461746103083Q00746F6E756D62657203093Q00496E76656E746F727900624Q008E7Q00206Q000100122Q000200028Q0002000200064Q0008000100010004443Q000800012Q00092Q0100014Q00BD000100023Q00120C2Q0100033Q00120C010200044Q005B00036Q00BA00010003000200067B0001001300013Q0004443Q0013000100120C010300054Q005B000400024Q00D500030002000200267400030015000100060004443Q001500012Q0009010300034Q00BD000300024Q000B000300013Q00067B0003001A00013Q0004443Q001A00012Q000B000300013Q0020060003000300070006F80003001E000100010004443Q001E00012Q0009010400044Q00BD000400024Q00E6000400033Q00200600050002000800200600060002000900200600070002000A2Q001401040003000100120C0105000B4Q005B000600044Q00110005000200070004443Q005D000100120C010A00054Q005B000B00094Q00D5000A00020002002668000A005D000100060004443Q005D000100120C010A000B4Q005B000B00094Q0011000A0002000C0004443Q005B000100120C010F00054Q005B0010000E4Q00D5000F00020002002668000F005B000100060004443Q005B000100120C010F000C4Q003B0010000E3Q00122Q0011000D6Q000F0011000200122Q0010000C6Q0011000E3Q00122Q0012000E6Q00100012000200122Q001100056Q0012000F6Q00110002000200262Q0011005B000100060004443Q005B000100120C011100054Q005B001200104Q00D50011000200020026680011005B000100060004443Q005B000100120C0111000C4Q005B0012000F3Q001200011300074Q008900110013000200063100110052000100030004443Q0052000100120C0112000F4Q005B001300114Q00D50012000200020006980012005B000100030004443Q005B000100120C011200053Q0012CA0013000C6Q001400103Q00122Q001500106Q001300156Q00123Q000200262Q0012005B000100060004443Q005B00012Q00BD001000023Q00068B000A0030000100020004443Q0030000100068B00050027000100020004443Q002700012Q0009010500054Q00BD000500024Q00E33Q00017Q00053Q0003043Q007469636B03063Q0063616368656403023Q00676303083Q00726567697374727903073Q007265706C69636100334Q000B7Q00067B3Q000D00013Q0004443Q000D000100120C012Q00014Q00643Q000100024Q000100019Q0000014Q000100023Q00064Q000D000100010004443Q000D00012Q000B7Q0012002Q0100024Q00013Q00034Q000B3Q00034Q00DD3Q0001000200067B3Q001800013Q0004443Q001800012Q00ED7Q00122Q000100016Q0001000100024Q000100016Q00015Q00122Q000200036Q000100034Q000B000100044Q00DD0001000100022Q005B3Q00013Q00067B3Q002400013Q0004443Q002400012Q00ED7Q00122Q000100016Q0001000100024Q000100016Q00015Q00122Q000200046Q000100034Q000B000100054Q00DD0001000100022Q005B3Q00013Q00067B3Q003000013Q0004443Q003000012Q00ED7Q00122Q000100016Q0001000100024Q000100016Q00015Q00122Q000200056Q000100034Q00092Q0100024Q0001000100034Q00E33Q00017Q000E3Q0003043Q007479706503053Q00676574676303083Q0066756E6374696F6E03053Q007063612Q6C03053Q007461626C6503063Q0055736572496403053Q00706169727303063Q0072617767657403053Q00546F6B656E03043Q005461677303043Q0044617461030C3Q00506C6179657253746174757303083Q00746F6E756D62657203083Q004D6F76656D656E7400593Q00120C012Q00013Q00120C2Q0100024Q00D53Q000200020026743Q0007000100030004443Q000700012Q0009017Q00BD3Q00023Q00120C012Q00043Q00120C2Q0100024Q00FD000200014Q00BA3Q0002000100067B3Q001200013Q0004443Q0012000100120C010200014Q005B000300014Q00D500020002000200267400020014000100050004443Q001400012Q0009010200024Q00BD000200024Q000B00025Q00067B0002001900013Q0004443Q001900012Q000B00025Q0020060002000200060006F80002001D000100010004443Q001D00012Q0009010300034Q00BD000300023Q00120C010300074Q005B000400014Q00110003000200050004443Q0054000100120C010800014Q005B000900074Q00D500080002000200266800080054000100050004443Q0054000100120C010800084Q0002000900073Q00122Q000A00096Q0008000A000200122Q000900086Q000A00073Q00122Q000B000A6Q0009000B000200122Q000A00086Q000B00073Q00122Q000C000B6Q000A000C000200262Q000800540001000C0004443Q0054000100120C010B00014Q005B000C000A4Q00D5000B00020002002668000B0054000100050004443Q0054000100120C010B00014Q005B000C00094Q00D5000B00020002002668000B004B000100050004443Q004B000100120C010B00084Q005B000C00093Q001200010D00064Q0089000B000D0002000631000B0049000100020004443Q0049000100120C010C000D4Q005B000D000B4Q00D5000C00020002000698000C0054000100020004443Q005400012Q00BD000A00023Q0004443Q0054000100120C010B00013Q0012CA000C00086Q000D000A3Q00122Q000E000E6Q000C000E6Q000B3Q000200262Q000B0054000100050004443Q005400012Q00BD000A00023Q00068B00030021000100020004443Q002100012Q0009010300034Q00BD000300024Q00E33Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403093Q0050726F78696D697479030A3Q0047722Q656479204365792Q033Q0049734103053Q004D6F64656C030B3Q005072696D6172795061727403103Q0048756D616E6F6964522Q6F745061727403063Q00434672616D6503083Q004765745069766F7403083Q00426173655061727403083Q00506F736974696F6E030A3Q004C2Q6F6B566563746F72026Q00144000324Q00567Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004443Q000900010020D900013Q0001001200010300034Q00890001000300020006F80001000D000100010004443Q000D00012Q0009010200024Q00BD000200024Q0009010200023Q0020D9000300010004001200010500054Q008900030005000200067B0003002200013Q0004443Q002200010020060003000100060006F800030019000100010004443Q001900010020D9000300010001001200010500074Q008900030005000200067B0003001E00013Q0004443Q001E00010020060004000300080006A800020021000100040004443Q002100010020D90004000100092Q00D50004000200022Q005B000200043Q0004443Q002800010020D90003000100040012000105000A4Q008900030005000200067B0003002800013Q0004443Q0028000100200600020001000800067B0002002F00013Q0004443Q002F000100200600030002000B00200600040002000C0020E800040004000D2Q00F70003000300042Q00BD000300024Q0009010300034Q00BD000300024Q00E33Q00017Q00053Q0003043Q007479706503093Q004661766F726974657303053Q007461626C6503053Q0070616972733Q01114Q00E600015Q00067B3Q000F00013Q0004443Q000F000100120C010200013Q00200600033Q00022Q00D50002000200020026680002000F000100030004443Q000F000100120C010200043Q00200600033Q00022Q00110002000200040004443Q000D00010020D600010005000500068B0002000C000100020004443Q000C00012Q00BD000100024Q00E33Q00017Q00053Q0003043Q007479706503063Q00737472696E6703053Q006D61746368034A3Q005E25782578257825782578257825782578252D2578257825782578252D2578257825782578252D2578257825782578252D257825782578257825782578257825782578257825782578240001103Q00120C2Q0100014Q005B00026Q00D500010002000200267400010007000100020004443Q000700012Q00FD00016Q00BD000100023Q0020D900013Q0003001200010300044Q00890001000300020026680001000D000100050004443Q000D00012Q006200016Q00FD000100014Q00BD000100024Q00E33Q00017Q002E3Q0003283Q00706C617965722064617461206E6F7420666F756E6420286E6F206D6574686F6420776F726B65642903173Q00506C61796572206461746120666F756E64207669613A2003093Q00496E76656E746F727903223Q00696E76656E746F7279206E6F7420666F756E6420696E20706C617965722064617461028Q0003053Q00706169727303043Q007479706503063Q00737472696E6703063Q006E756D626572030D3Q00536B69704661766F726974657303043Q004D69736303053Q007461626C6503043Q004E616D6503083Q005175616E7469747903043Q004755494403043Q004F72657303053Q0052756E657303073Q005570677261646503043Q005479706503063Q00547261697473026Q00F03F03023Q00496403043Q005469657203053Q00547261697403063Q006970616972730003053Q0056616C756503063Q00416D6F756E7403053Q00506F77657203053Q004C6576656C03043Q005374617403063Q00696E7365727403043Q006E616D6503053Q0076616C756503043Q007469657203093Q0044656275674D6F646503053Q007072696E7403063Q00666F726D6174032B3Q005B53652Q6C2044656275675D2054726169743A2025732C2056616C75653A2025732C20546965723A20256403083Q00746F737472696E6703053Q0025733D257303163Q005B53652Q6C2044656275675D205261774B6579733A2003063Q00636F6E63617403023Q002C2003043Q006E65787403173Q006E6F2073652Q6C61626C65206974656D7320666F756E64003E013Q000B8Q00FA3Q000100010006F83Q0007000100010004443Q000700012Q0009010200023Q001200010300014Q0001000200034Q000B000200013Q001214000300026Q000400016Q0003000300044Q00020002000100202Q00023Q000300062Q00020012000100010004443Q001200012Q0009010300033Q001200010400044Q0001000300034Q000B000300024Q000D00048Q0003000200024Q00045Q00122Q000500053Q00122Q000600066Q000700026Q00060002000800044Q0039000100120C010B00074Q005B000C00094Q00D5000B00020002002668000B0039000100080004443Q0039000100120C010B00074Q005B000C000A4Q00D5000B00020002002668000B0039000100090004443Q00390001000ED2000500390001000A0004443Q003900012Q000B000B00034Q0082000B000B000900067B000B003900013Q0004443Q003900012Q000B000B00044Q005B000C00094Q00D5000B0002000200067B000B003900013Q0004443Q003900012Q000B000B00053Q002006000B000B000A00067B000B003700013Q0004443Q003700012Q0082000B000300090006F8000B0039000100010004443Q003900012Q00BF00040009000A2Q00F700050005000A00068B0006001B000100020004443Q001B000100200600060002000B00120C010700074Q005B000800064Q00D5000700020002002668000700312Q01000C0004443Q00312Q0100120C010700064Q005B000800064Q00110007000200090004443Q002F2Q0100120C010C00074Q005B000D000B4Q00D5000C00020002002668000C002F2Q01000C0004443Q002F2Q01002006000C000B000D002006000D000B000E002006000E000B000F2Q00FD000F5Q00067B000C006C00013Q0004443Q006C00012Q000B001000064Q008200100010000C00067B0010006C00013Q0004443Q006C000100067B000D006C00013Q0004443Q006C0001000ED20005006C0001000D0004443Q006C00012Q000B001000074Q005B0011000C4Q00D500100002000200067B0010006C00013Q0004443Q006C00012Q000B001000053Q00200600100010000A00067B0010006400013Q0004443Q006400012Q008200100003000C0006F80010006C000100010004443Q006C00012Q008200100004000C0006F800100068000100010004443Q00680001001200011000054Q00F700100010000D2Q00BF0004000C00102Q00F700050005000D2Q00FD000F00013Q0006F8000F002F2Q0100010004443Q002F2Q0100067B000E002F2Q013Q0004443Q002F2Q010020060010000B00100006F80010007A000100010004443Q007A00010020060010000B00110006F80010007A000100010004443Q007A00010020060010000B00120006F80010007A000100010004443Q007A00010020060010000B00130006F80010002F2Q0100010004443Q002F2Q012Q00E600115Q0020060012000B00140006F800120081000100010004443Q008100012Q00E600125Q00120C011300074Q005B001400124Q00D5001300020002002668001300202Q01000C0004443Q00202Q0100120C011300064Q005B001400124Q00110013000200150004443Q001E2Q012Q0009011800193Q001223001A00153Q00122Q001B00076Q001C00176Q001B0002000200262Q001B0093000100080004443Q009300012Q005B001800173Q0004443Q00DD000100120C011B00074Q005B001C00174Q00D5001B00020002002668001B00DD0001000C0004443Q00DD0001002006001B0017001300067B001B00AC00013Q0004443Q00AC000100120C011B00073Q002006001C001700132Q00D5001B00020002002668001B00AC0001000C0004443Q00AC0001002006001B00170013002006001B001B00160006A8001800A60001001B0004443Q00A60001002006001B001700130020060018001B000D002006001B00170013002006001B001B00170006A8001A00AB0001001B0004443Q00AB0001001200011A00153Q0004443Q00B70001002006001B001700160006A8001800B30001001B0004443Q00B30001002006001B0017000D0006A8001800B30001001B0004443Q00B30001002006001800170018002006001B001700170006A8001A00B70001001B0004443Q00B70001001200011A00153Q00067B001800CE00013Q0004443Q00CE00012Q000B001B00084Q0082001B001B001800067B001B00C800013Q0004443Q00C8000100120C011C00194Q005B001D001B4Q0011001C0002001E0004443Q00C600012Q0082002100170020002674002100C60001001A0004443Q00C600012Q005B001900213Q0004443Q00C8000100068B001C00C1000100020004443Q00C100010006F8001900CE000100010004443Q00CE00012Q0082001C00170018002674001C00CE0001001A0004443Q00CE00012Q00820019001700180006F8001900DD000100010004443Q00DD0001002006001B0017001B0006A8001900DD0001001B0004443Q00DD0001002006001B0017001C0006A8001900DD0001001B0004443Q00DD0001002006001B0017001D0006A8001900DD0001001B0004443Q00DD0001002006001B0017001E0006A8001900DD0001001B0004443Q00DD000100200600190017001F00120C011B00074Q005B001C00184Q00D5001B00020002002668001B001E2Q0100080004443Q001E2Q0100120C011B000C3Q00208A001B001B00204Q001C00116Q001D3Q000300102Q001D0021001800102Q001D0022001900102Q001D0023001A4Q001B001D00014Q001B00053Q00202Q001B001B002400062Q001B001E2Q013Q0004443Q001E2Q0100120C011B00253Q001204001C00083Q00202Q001C001C002600122Q001D00273Q00122Q001E00286Q001F00186Q001E0002000200122Q001F00286Q002000196Q001F000200024Q0020001A6Q001C00206Q001B3Q000100122Q001B00076Q001C00176Q001B0002000200262Q001B001E2Q01000C0004443Q001E2Q012Q00E6001B5Q00120C011C00064Q005B001D00174Q0011001C0002001E0004443Q00132Q0100120C0121000C3Q0020F00021002100204Q0022001B3Q00122Q002300083Q00202Q00230023002600122Q002400293Q00122Q002500286Q0026001F6Q00250002000200122Q002600286Q002700206Q002600276Q00238Q00213Q000100068B001C00052Q0100020004443Q00052Q0100120C011C00253Q00129D001D002A3Q00122Q001E000C3Q00202Q001E001E002B4Q001F001B3Q00122Q0020002C6Q001E002000024Q001D001D001E4Q001C0002000100068B0013008A000100020004443Q008A00012Q000B001300094Q005B001400114Q005B0015000C4Q008900130015000200067B0013002F2Q013Q0004443Q002F2Q012Q000B001300053Q00200600130013000A00067B0013002D2Q013Q0004443Q002D2Q012Q008200130003000E0006F80013002F2Q0100010004443Q002F2Q010020D60004000E00150020C000050005001500068B00070045000100020004443Q0045000100120C0107002D4Q005B000800044Q00D5000700020002002668000700392Q01001A0004443Q00392Q012Q0009010700073Q0012000108002E4Q0001000700034Q005B000700044Q0009010800084Q005B000900054Q002E000700024Q00E33Q00017Q00043Q00030E3Q0046696E6446697273744368696C6403063Q004C6976696E6703043Q004E616D6503093Q00436861726163746572000F4Q000A016Q00206Q000100122Q000200028Q0002000200064Q000B00013Q0004443Q000B00010020D900013Q00012Q000B000300013Q0020060003000300032Q0087000100034Q005300016Q000B000100013Q0020060001000100042Q00BD000100024Q00E33Q00017Q00023Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727401073Q0006950001000500013Q0004443Q000500010020D900013Q0001001200010300024Q00890001000300022Q00BD000100024Q00E33Q00017Q00103Q0003083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503103Q0053652Q6C4D6F64756C6543617270657403043Q0053697A6503073Q00566563746F7233026Q001840026Q00E03F030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C696465010003063Q00506172656E74001D4Q000B7Q00067B3Q000400013Q0004443Q000400012Q00E33Q00013Q00120C012Q00013Q0020B25Q000200122Q000100038Q000200029Q009Q0000304Q000400059Q0000122Q000100073Q00202Q00010001000200122Q000200083Q00122Q000300093Q00122Q000400086Q00010004000200104Q000600019Q0000304Q000A000B9Q0000304Q000C000D9Q0000304Q000E000F9Q004Q000100013Q00104Q001000016Q00017Q00043Q0003063Q00506172656E7403063Q00434672616D652Q033Q006E6577028Q0001144Q000B00015Q00067B0001000800013Q0004443Q0008000100067B3Q000800013Q0004443Q0008000100200600013Q00010006F800010009000100010004443Q000900012Q00E33Q00014Q000B00015Q00201300023Q000200122Q000300023Q00202Q00030003000300122Q000400046Q000500013Q00122Q000600046Q0003000600024Q00020002000300102Q0001000200026Q00017Q00013Q0003073Q0044657374726F7900094Q000B7Q00067B3Q000800013Q0004443Q000800012Q000B7Q0020D95Q00012Q000E012Q000200012Q0009017Q00ED8Q00E33Q00017Q00113Q00030A3Q00446973636F2Q6E656374030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q00506C6174666F726D5374616E64010003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103073Q0044657374726F7903103Q0053652Q6C426F6479506F736974696F6E00504Q00FD8Q00ED8Q000B3Q00013Q00067B3Q000A00013Q0004443Q000A00012Q000B3Q00013Q0020D95Q00012Q000E012Q000200012Q0009017Q00ED3Q00014Q000B3Q00023Q00067B3Q001200013Q0004443Q001200012Q000B3Q00023Q0020D95Q00012Q000E012Q000200012Q0009017Q00ED3Q00024Q000B3Q00034Q00DD3Q0001000200067B3Q003700013Q0004443Q003700012Q000B000100044Q00A900028Q00010002000200202Q00023Q000200122Q000400036Q00020004000200062Q0001002400013Q0004443Q0024000100120C010300053Q00204B00030003000600102Q00010004000300122Q000300053Q00202Q00030003000600102Q00010007000300067B0002002A00013Q0004443Q002A000100200600030002000800067B0003002A00013Q0004443Q002A000100307200020008000900120C0103000A3Q0020D900043Q000B2Q0043000400054Q007700033Q00050004443Q003500010020D900080007000C001200010A000D4Q00890008000A000200067B0008003500013Q0004443Q003500010030720007000E000F00068B0003002F000100020004443Q002F00012Q000B000100053Q00067B0001003F00013Q0004443Q003F00012Q000B000100053Q0020D90001000100102Q000E2Q01000200012Q00092Q0100014Q00ED000100053Q00067B3Q004D00013Q0004443Q004D00012Q000B000100044Q005B00026Q00D500010002000200067B0001004D00013Q0004443Q004D00010020D9000200010002001200010400114Q008900020004000200067B0002004D00013Q0004443Q004D00010020D90003000200102Q000E0103000200012Q000B000100064Q000F0001000100012Q00E33Q00017Q00163Q0003043Q007461736B03043Q0077616974029A5Q99B93F030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403213Q00466C79546F206661696C65643A20436861726163746572206E6F7420666F756E64030D3Q00506C6174666F726D5374616E642Q0103163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F6369747903053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964650100030B3Q00466C79696E6720746F3A202Q033Q004E504303093Q0048656172746265617403073Q00436F2Q6E65637402564Q000B00025Q00067B0002000900013Q0004443Q000900012Q000B000200014Q001E00020001000100122Q000200013Q00202Q00020002000200122Q000300036Q0002000200012Q000B000200024Q00110102000100024Q000300036Q000400026Q00030002000200062Q00040013000100020004443Q001300010020D9000400020004001200010600054Q008900040006000200067B0003001700013Q0004443Q001700010006F80004001B000100010004443Q001B00012Q000B000500043Q001200010600064Q000E0105000200012Q00E33Q00013Q0030720004000700080012760005000A3Q00202Q00050005000B00102Q00030009000500122Q0005000A3Q00202Q00050005000B00102Q0003000C00050012490005000D3Q00202Q00060002000E4Q000600076Q00053Q000700044Q002D00010020D9000A0009000F001200010C00104Q0089000A000C000200067B000A002D00013Q0004443Q002D000100307200090011001200068B00050027000100020004443Q002700012Q00FD000500014Q009F00058Q000500056Q0005000100014Q000500066Q000600036Q0005000200014Q000500043Q00122Q000600133Q00062Q0007003B000100010004443Q003B0001001200010700144Q00F30006000600072Q000E0105000200012Q000B000500083Q0020060005000500150020D900050005001600066700073Q000100022Q000B8Q000B3Q00024Q00070005000700024Q000500076Q000500083Q00202Q00050005001500202Q000500050016000667000700010001000A2Q000B8Q000B3Q00024Q000B3Q00034Q000B3Q00064Q005B8Q000B3Q000A4Q000B3Q00044Q000B3Q00014Q000B3Q000B4Q000B3Q000C4Q00890005000700022Q00ED000500094Q00E33Q00013Q00023Q00063Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465012Q001A4Q000B7Q0006F83Q0004000100010004443Q000400012Q00E33Q00014Q000B3Q00014Q00DD3Q000100020006F83Q0009000100010004443Q000900012Q00E33Q00013Q00120C2Q0100013Q0020D900023Q00022Q0043000200034Q007700013Q00030004443Q001700010020D9000600050003001200010800044Q008900060008000200067B0006001700013Q0004443Q0017000100200600060005000500067B0006001700013Q0004443Q0017000100307200050005000600068B0001000E000100020004443Q000E00012Q00E33Q00017Q00263Q00030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030D3Q00506C6174666F726D5374616E642Q0103083Q00506F736974696F6E03093Q004D61676E697475646503163Q00412Q72697665642061742064657374696E6174696F6E026Q11913F03043Q00556E697403043Q006D6174682Q033Q006D696E03083Q00496E7374616E63652Q033Q006E657703083Q00426F64794779726F03093Q004D6178546F7271756503073Q00566563746F7233024Q00652QCD4103013Q0050025Q0088C34003013Q0044026Q00594003063Q00506172656E7403013Q005803013Q005903013Q005A029A5Q99B93F03063Q00434672616D6503063Q006C2Q6F6B417403103Q0053652Q6C426F6479506F736974696F6E030C3Q00426F6479506F736974696F6E03043Q004E616D6503083Q004D6178466F726365024Q0080842E41025Q006AE840025Q00408F4003163Q00412Q73656D626C794C696E65617256656C6F6369747903043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479017F4Q000B00015Q0006F800010004000100010004443Q000400012Q00E33Q00014Q000B000100014Q00112Q01000100024Q000200026Q000300016Q00020002000200062Q0003000E000100010004443Q000E00010020D9000300010001001200010500024Q008900030005000200067B0002001200013Q0004443Q001200010006F800030013000100010004443Q001300012Q00E33Q00014Q000B000400034Q005B000500024Q000E0104000200010020060004000300030006F80004001A000100010004443Q001A00010030720003000300040020060004000200052Q0021000500046Q00050005000400202Q0006000500064Q000700053Q00062Q00060027000100070004443Q002700012Q000B000700063Q00125A000800076Q0007000200014Q000700076Q0007000100016Q00014Q000B000700083Q0006A80008002B00013Q0004443Q002B0001001200010800084Q000601070007000800207A00080005000900122Q0009000A3Q00202Q00090009000B4Q000A00076Q000B00066Q0009000B00024Q000A000800094Q000A0004000A4Q000B00093Q00062Q000B004A000100010004443Q004A000100120C010B000C3Q0020E9000B000B000D00122Q000C000E6Q000B000200024Q000B00096Q000B00093Q00122Q000C00103Q00202Q000C000C000D00122Q000D00113Q00122Q000E00113Q00122Q000F00116Q000C000F000200102Q000B000F000C4Q000B00093Q00302Q000B001200134Q000B00093Q00302Q000B001400154Q000B00093Q00102Q000B0016000200120C010B00103Q00207E000B000B000D4Q000C00043Q00202Q000C000C001700202Q000D000A00184Q000E00043Q00202Q000E000E00194Q000B000E00024Q000C000B000A00202Q000C000C0006000E2Q001A005D0001000C0004443Q005D00012Q000B000D00093Q001292000E001B3Q00202Q000E000E001C4Q000F000A6Q0010000B6Q000E0010000200102Q000D001B000E0020D9000D00020001001200010F001D4Q0089000D000F00020006F8000D0072000100010004443Q0072000100120C010E000C3Q002057000E000E000D00122Q000F001E6Q000E000200024Q000D000E3Q00302Q000D001F001D00122Q000E00103Q00202Q000E000E000D00122Q000F00213Q00122Q001000213Q00122Q001100216Q000E0011000200102Q000D0020000E00302Q000D0012002200302Q000D0014002300102Q000D0016000200101C000D0005000A001229000E001B3Q00202Q000E000E000D4Q000F000A6Q000E0002000200102Q0002001B000E00122Q000E00103Q00202Q000E000E002500102Q00020024000E00122Q000E00103Q00202Q000E000E002500102Q00020026000E6Q00017Q000F3Q00030D3Q00466F7263654469616C6F67756503083Q004469616C6F67756503053Q007063612Q6C010003103Q0053652Q6C4469616C6F6775654D697363026Q00F83F030D3Q004469616C6F6775654576656E7403043Q007461736B03043Q0077616974026Q00E03F00030F3Q0053652Q6C436F6E6669726D4D697363027Q004003383Q005761726E696E673A2053652Q6C436F6E6669726D4D697363206E6F74206F627365727665642C20636F6E74696E75696E6720616E7977617903043Q007469636B02733Q00067B3Q000A00013Q0004443Q000A000100200600023Q000100067B0002000A00013Q0004443Q000A000100200600023Q000200067B0002000A00013Q0004443Q000A00010006F80001000C000100010004443Q000C00012Q00FD00026Q00BD000200023Q00120C010200033Q00066700033Q000100022Q005B8Q005B3Q00014Q001100020002000300067B0002002600013Q0004443Q0026000100267400030026000100040004443Q002600012Q000B00045Q001200010500053Q001200010600064Q008900040006000200067B0004002600013Q0004443Q0026000100200600053Q000700067B0005002600013Q0004443Q0026000100120C010500033Q00066700060001000100012Q005B8Q000E01050002000100120C010500033Q00066700060002000100012Q005B8Q000E0105000200012Q00FD00045Q00120C010500033Q00066700060003000100022Q005B8Q005B3Q00014Q00110005000200062Q005B000300064Q005B000200053Q00067B0002003300013Q0004443Q0033000100267400030033000100040004443Q003300012Q00FD000400013Q0006F800040043000100010004443Q0043000100120C010500083Q0020060005000500090012000106000A4Q000E01050002000100120C010500033Q00066700060004000100022Q005B8Q005B3Q00014Q001100050002000600067B0005004300013Q0004443Q0043000100267400060043000100040004443Q004300012Q00FD000400013Q0006F80004004A000100010004443Q004A000100067B0002004A00013Q0004443Q004A00010026680003004A0001000B0004443Q004A00012Q00FD000400013Q0006F80004004E000100010004443Q004E00012Q00FD00056Q00BD000500024Q000B00055Q0012000106000C3Q0012000107000D4Q00BA0005000700060006F80005005E000100010004443Q005E000100120C010700083Q00201B00070007000900122Q0008000A6Q0007000200014Q00075Q00122Q0008000C3Q00122Q0009000D6Q0007000900084Q000600086Q000500073Q0006F800050063000100010004443Q006300012Q000B000700013Q0012000108000E4Q000E01070002000100067B0006006900013Q0004443Q006900012Q00ED000600023Q00120C0107000F4Q00DD0007000100022Q00ED000700033Q00200600073Q000700067B0007007000013Q0004443Q0070000100120C010700033Q00066700080005000100012Q005B8Q000E0107000200012Q00FD000700014Q00BD000700024Q00E33Q00013Q00063Q00023Q0003083Q004469616C6F677565030C3Q00496E766F6B6553657276657200074Q00617Q00206Q000100206Q00024Q000200018Q00029Q008Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00107Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q00436C6F73656400064Q00107Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q00466F7263654469616C6F677565030C3Q00496E766F6B65536572766572030F3Q0053652Q6C436F6E6669726D4D69736300084Q002D7Q00206Q000100206Q00024Q000200013Q00122Q000300038Q00039Q008Q00017Q00033Q00030D3Q00466F7263654469616C6F677565030C3Q00496E766F6B65536572766572030F3Q0053652Q6C436F6E6669726D4D69736300084Q002D7Q00206Q000100206Q00024Q000200013Q00122Q000300038Q00039Q008Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00107Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403063Q00537461747573030F3Q0044697361626C654261636B7061636B03283Q0052656D6F76696E672044697361626C654261636B7061636B207461672066726F6D2053746174757303053Q007063612Q6C030D3Q004469616C6F6775654576656E7403093Q00506C61796572477569030A3Q004469616C6F677565554903053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q0047756942752Q746F6E03113Q00526573706F6E736542692Q6C626F617264014D3Q0006F83Q0003000100010004443Q000300012Q00E33Q00014Q000B00016Q00DD00010001000200067B0001001900013Q0004443Q001900010020D9000200010001001200010400024Q008900020004000200067B0002001900013Q0004443Q001900010020D9000300020001001200010500034Q008900030005000200067B0003001800013Q0004443Q001800012Q000B000400013Q001200010500044Q000E01040002000100120C010400053Q00066700053Q000100012Q005B3Q00034Q000E0104000200012Q00DC00035Q00200600023Q000600067B0002002000013Q0004443Q0020000100120C010200053Q00066700030001000100012Q005B8Q000E01020002000100120C010200053Q00066700030002000100012Q000B3Q00024Q004E0002000200014Q000200033Q00202Q00020002000100122Q000400076Q00020004000200062Q0002004C00013Q0004443Q004C00010020D9000300020001001200010500084Q008900030005000200067B0003004000013Q0004443Q0040000100120C010400093Q0020D900050003000A2Q0043000500064Q007700043Q00060004443Q003E00010020D900090008000B001200010B000C4Q00890009000B000200067B0009003D00013Q0004443Q003D000100120C010900053Q000667000A0003000100012Q005B3Q00084Q000E0109000200012Q00DC00075Q00068B00040034000100020004443Q0034000100069500040045000100030004443Q004500010020D90004000300010012000106000D4Q008900040006000200067B0004004B00013Q0004443Q004B000100120C010500053Q00066700060004000100012Q005B3Q00044Q000E0105000200012Q00DC00036Q00E33Q00013Q00053Q00013Q0003073Q0044657374726F7900044Q000B7Q0020D95Q00012Q000E012Q000200012Q00E33Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q00436C6F73656400064Q00107Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030E3Q0053656C65637465644F626A65637400030E3Q00436C65617253656C656374696F6E000A4Q002C7Q00304Q000100029Q0000206Q000300064Q000900013Q0004443Q000900012Q000B7Q0020D95Q00032Q000E012Q000200012Q00E33Q00017Q00033Q0003073Q0056697369626C650100030C3Q00496E74657261637461626C6500054Q00A17Q00304Q000100029Q0000304Q000300026Q00017Q00023Q0003073Q0056697369626C65012Q00034Q000B7Q0030723Q000100022Q00E33Q00017Q00533Q0003043Q007469636B03093Q004175746F2053652Q6C03083Q004E6F206974656D73027Q004003123Q004261736B6574206275696C7420776974682003063Q00206974656D73030A3Q0052756E436F2Q6D616E64030D3Q00466F7263654469616C6F67756503083Q004469616C6F67756503113Q0052656D6F746573206E6F7420666F756E64026Q00084003183Q004E50432047722Q65647920436579206E6F7420666F756E64030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403063Q00434672616D6503093Q0057616C6B53702Q6564026Q00304003093Q004A756D70506F776572026Q004940030D3Q00666F72636554656C65706F7274030A3Q006E6F54656C65706F7274031C3Q0053652Q6C4F6E63652063612Q6C65643A206E6F54656C65706F72743D03083Q00746F737472696E6703103Q002C20666F72636554656C65706F72743D03303Q005573696E672063616368656420636F6E74657874202D20736B692Q70696E67204F70656E53652Q6C4469616C6F67756503133Q004F70656E696E67206469616C6F6775653Q2E030D3Q006469616C6F674F70656E65643D030D3Q002C206E6F54656C65706F72743D03153Q002C20486173496E697469616C697A656453652Q6C3D03143Q004E6F54656C65706F72744166746572466972737403373Q0052657475726E696E67206561726C79202D206469616C6F67206E6F74206F70656E656420616E64206E6F54656C65706F7274206D6F646503353Q004469616C6F6720746964616B20646170617420646962756B612074616E70612074656C65706F72742E2044656B617469204E50432E03163Q004E504320706F736974696F6E206E6F7420666F756E6403133Q00436861726163746572206E6F7420666F756E64031C3Q0054656C65706F7274696E6720746F2047722Q656479204365793Q2E2Q033Q006E657703163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F6369747903043Q007461736B03043Q0077616974029A5Q99B93F03173Q004661696C656420746F206F70656E206469616C6F67756503223Q0053656E64696E672053652Q6C436F6E6669726D2077697468206261736B65743Q2E03053Q007063612Q6C010003133Q00436C6F73696E67206469616C6F6775653Q2E03103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E030B3Q005072696D61727950617274028Q0003323Q0054656C65706F7274696E67206177617920746F207472692Q676572206469616C6F677565206175746F2D636C6F73653Q2E026Q33F33F03213Q0052657475726E696E6720746F206F726967696E616C20706F736974696F6E3Q2E03063Q00737472696E6703063Q00666F726D6174030D3Q00536F6C64202564206974656D73030D3Q0053652Q6C2053552Q43452Q5321030B3Q0053652Q6C206661696C6564030B3Q0053652Q6C204641494C454403063Q0053746174757303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q00422Q6F6C56616C756503043Q004E616D65031B3Q0052656D6F76696E672053746174757320422Q6F6C56616C75653A20030B3Q004E756D62657256616C756503053Q006C6F77657203043Q0066696E64030C3Q0064617368632Q6F6C646F776E03253Q00526573652Q74696E67206461736820632Q6F6C646F776E204E756D62657256616C75653A202Q033Q00203D2003053Q0056616C7565030D3Q00506C6174666F726D5374616E642Q033Q0053697403163Q0057616C6B53702Q656420726573746F72656420746F2003163Q004A756D70506F77657220726573746F72656420746F2003083Q00416E63686F726564031B3Q0048756D616E6F6964522Q6F745061727420756E616E63686F72656403053Q0064656C6179026Q00E03F011B023Q000B00015Q00067B0001000500013Q0004443Q000500012Q00FD00016Q00BD000100024Q00FD000100014Q004C00018Q000100016Q000200016Q0001000200014Q000100026Q00010001000300062Q0001001F000100010004443Q001F00012Q00FD00046Q008400045Q00122Q000400016Q0004000100024Q000400036Q000400043Q00122Q000500023Q00062Q00060018000100020004443Q00180001001200010600033Q001200010700044Q00220004000700014Q000400016Q00058Q0004000200014Q00048Q000400024Q000B000400053Q0012A7000500056Q000600033Q00122Q000700066Q0005000500074Q0004000200014Q000400066Q00040001000200202Q00050004000700062Q0005003000013Q0004443Q0030000100200600050004000800067B0005003000013Q0004443Q003000010020060005000400090006F80005003C000100010004443Q003C00012Q00FD00056Q00DB00058Q000500043Q00122Q000600023Q00122Q0007000A3Q00122Q0008000B6Q0005000800014Q000500016Q00068Q0005000200014Q00058Q000500024Q000B000500074Q00DD0005000100020006F80005004C000100010004443Q004C00012Q00FD00066Q00DB00068Q000600043Q00122Q000700023Q00122Q0008000C3Q00122Q0009000B6Q0006000900014Q000600016Q00078Q0006000200014Q00068Q000600024Q000B000600084Q00110106000100024Q000700096Q000800066Q00070002000200062Q00080056000100060004443Q005600010020D900080006000D001200010A000E4Q00890008000A000200069500090059000100070004443Q0059000100200600090007000F2Q00FD000A5Q00067B0008005F00013Q0004443Q005F0001002006000B000800100006F8000B0060000100010004443Q00600001001200010B00113Q00067B0008006500013Q0004443Q00650001002006000C000800120006F8000C0066000100010004443Q00660001001200010C00133Q000695000D006900013Q0004443Q00690001002006000D3Q0014000695000E006C00013Q0004443Q006C0001002006000E3Q00152Q000B000F00053Q001202011000163Q00122Q001100176Q0012000E6Q00110002000200122Q001200183Q00122Q001300176Q0014000D6Q0013000200024Q0010001000134Q000F0002000100062Q000D007B00013Q0004443Q007B00012Q00FD000F6Q00ED000F000A4Q00FD000F6Q00120110000B6Q001100046Q0010000200024Q000F00103Q00062Q000F008600013Q0004443Q008600012Q000B001000053Q001200011100194Q000E0110000200010004443Q008E00012Q000B001000053Q0012580011001A6Q0010000200014Q0010000C6Q001100046Q001200056Q0010001200024Q000F00104Q000B001000053Q002Q120011001B3Q00122Q001200176Q0013000F6Q00120002000200122Q0013001C3Q00122Q001400176Q0015000E6Q00140002000200122Q0015001D3Q00122Q001600176Q0017000A6Q0016000200024Q0011001100164Q00100002000100062Q000F00B9000100010004443Q00B900010006F8000E00A8000100010004443Q00A800012Q000B0010000A3Q00067B001000B900013Q0004443Q00B900012Q000B0010000D3Q00200600100010001E00067B001000B900013Q0004443Q00B900012Q000B001000053Q0012990011001F6Q0010000200014Q00108Q00105Q00062Q000E00B4000100010004443Q00B400012Q000B001000043Q001200011100023Q001200011200203Q0012000113000B4Q00B10010001300012Q000B001000014Q00FD00116Q000E0110000200012Q00FD00106Q00BD001000023Q0006F8000F00F6000100010004443Q00F600010006F8000E00F6000100010004443Q00F600012Q000B0010000E4Q00DD0010000100020006F8001000CD000100010004443Q00CD00012Q00FD00116Q00DB00118Q001100043Q00122Q001200023Q00122Q001300213Q00122Q0014000B6Q0011001400014Q001100016Q00128Q0011000200014Q00118Q001100023Q0006F8000700DB000100010004443Q00DB00012Q00FD00116Q00DB00118Q001100043Q00122Q001200023Q00122Q001300223Q00122Q0014000B6Q0011001400014Q001100016Q00128Q0011000200014Q00118Q001100024Q000B001100053Q00127D001200236Q0011000200014Q000A00013Q00122Q0011000F3Q00202Q0011001100244Q001200106Q00110002000200102Q0007000F001100122Q001100263Q00202Q00110011002700102Q00070025001100122Q001100263Q00202Q00110011002700102Q00070028001100122Q001100293Q00202Q00110011002A00122Q0012002B6Q0011000200014Q001100053Q00122Q0012001A6Q0011000200014Q0011000C6Q001200046Q001300056Q0011001300024Q000F00113Q0006F8000F00132Q0100010004443Q00132Q0100067B000A00052Q013Q0004443Q00052Q0100067B000900052Q013Q0004443Q00052Q0100067B000700052Q013Q0004443Q00052Q0100101C0007000F0009001276001000263Q00202Q00100010002700102Q00070025001000122Q001000263Q00202Q00100010002700102Q0007002800102Q00FD00106Q00FE0010000A6Q00108Q00108Q001000043Q00122Q001100023Q00122Q0012002C3Q00122Q0013000B6Q0010001300014Q001000016Q00118Q0010000200014Q00108Q001000024Q00FD001000014Q00E50010000A6Q001000053Q00122Q0011002D6Q0010000200014Q00105Q00122Q0011002E3Q00066700123Q000100022Q005B3Q00044Q005B3Q00014Q001100110002001200067B001100232Q013Q0004443Q00232Q01002674001200232Q01002F0004443Q00232Q012Q00FD001000013Q00120C011300293Q0020C500130013002A00122Q0014002B6Q0013000200014Q001300053Q00122Q001400306Q0013000200014Q0013000F6Q001400046Q0013000200014Q001300016Q00148Q00130002000100062Q000E005D2Q0100010004443Q005D2Q0100067B0007005D2Q013Q0004443Q005D2Q0100067B0005005D2Q013Q0004443Q005D2Q0100200600130005003100067B0013003D2Q013Q0004443Q003D2Q010020060013000500310020060013001300320006F8001300422Q0100010004443Q00422Q0100200600130005003300067B001300422Q013Q0004443Q00422Q0100200600130005003300200600130013003200067B0013005D2Q013Q0004443Q005D2Q0100120C011400263Q00200A00140014002400122Q001500133Q00122Q001600343Q00122Q001700136Q0014001700024Q0014001300144Q001500053Q00122Q001600356Q00150002000100122Q0015000F3Q00202Q0015001500244Q001600146Q00150002000200102Q0007000F001500122Q001500263Q00202Q00150015002700102Q00070025001500122Q001500263Q00202Q00150015002700102Q00070028001500122Q001500293Q00202Q00150015002A00122Q001600366Q00150002000100067B000A00712Q013Q0004443Q00712Q0100067B000900712Q013Q0004443Q00712Q0100067B000700712Q013Q0004443Q00712Q012Q000B001300053Q0012E0001400376Q00130002000100102Q0007000F000900122Q001300263Q00202Q00130013002700102Q00070025001300122Q001300263Q00202Q00130013002700102Q00070028001300122Q001300293Q00202Q00130013002A00122Q0014002B6Q00130002000100067B001000832Q013Q0004443Q00832Q0100120C011300014Q00AD0013000100024Q001300036Q001300043Q00122Q001400023Q00122Q001500383Q00202Q00150015003900122Q0016003A6Q001700036Q00150017000200122Q001600046Q0013001600014Q001300053Q00122Q0014003B6Q00130002000100044Q008B2Q012Q000B001300043Q0012EB001400023Q00122Q0015003C3Q00122Q0016000B6Q0013001600014Q001300053Q00122Q0014003D6Q0013000200012Q00FD00136Q009B00138Q001300106Q001400086Q00140001000200062Q001500952Q0100140004443Q00952Q010020D900150014000D0012000117000E4Q00890015001700020006950016009A2Q0100140004443Q009A2Q010020D900160014000D001200011800314Q008900160018000200067B0015001902013Q0004443Q001902010020D900170014000D0012000119003E4Q008900170019000200067B001700D62Q013Q0004443Q00D62Q0100120C0118003F3Q0020D90019001700402Q00430019001A4Q007700183Q001A0004443Q00D42Q010020D9001D001C0041001200011F00424Q0089001D001F000200067B001D00B92Q013Q0004443Q00B92Q012Q000B001D00103Q002006001E001C00432Q00D5001D0002000200067B001D00B92Q013Q0004443Q00B92Q012Q000B001D00053Q0012CC001E00443Q00202Q001F001C00434Q001E001E001F4Q001D0002000100122Q001D002E3Q000667001E0001000100012Q005B3Q001C4Q000E011D000200010020D9001D001C0041001200011F00454Q0089001D001F000200067B001D00D32Q013Q0004443Q00D32Q01002006001D001C004300203E001D001D00464Q001D0002000200202Q001D001D004700122Q001F00486Q001D001F000200062Q001D00D32Q013Q0004443Q00D32Q012Q000B001D00053Q001273001E00493Q00202Q001F001C004300122Q0020004A3Q00122Q002100173Q00202Q0022001C004B4Q0021000200024Q001E001E00214Q001D0002000100122Q001D002E3Q000667001E0002000100012Q005B3Q001C4Q000E011D000200012Q00DC001B5Q00068B001800A62Q0100020004443Q00A62Q010030720015004C002F0030720015004D002F002006001800150010002674001800DE2Q0100340004443Q00DE2Q01002006001800150010000678001800E42Q01000B0004443Q00E42Q0100101C00150010000B2Q00BC001800053Q00122Q0019004E6Q001A000B6Q00190019001A4Q001800020001002006001800150012002674001800EA2Q0100340004443Q00EA2Q01002006001800150012000678001800F02Q01000C0004443Q00F02Q0100101C00150012000C2Q00BC001800053Q00122Q0019004F6Q001A000C6Q00190019001A4Q00180002000100067B001600F92Q013Q0004443Q00F92Q0100200600180016005000067B001800F92Q013Q0004443Q00F92Q0100307200160050002F2Q000B001800053Q001200011900514Q000E01180002000100120C0118002E3Q00066700190003000100012Q005B3Q00154Q000E01180002000100120C0118002E3Q00066700190004000100032Q000B3Q00114Q000B3Q00124Q000B3Q00054Q000E01180002000100120C0118002E3Q00066700190005000100032Q000B3Q00134Q000B3Q00124Q000B3Q00054Q000E01180002000100120C0118002E3Q00066700190006000100022Q000B3Q00134Q000B3Q00054Q000E01180002000100120C011800293Q002006001800180052001200011900533Q000667001A0007000100062Q005B3Q00154Q005B3Q000B4Q005B3Q000C4Q005B3Q00164Q000B3Q00084Q000B3Q00104Q00B10018001A00012Q00BD001300024Q00E33Q00013Q00083Q00043Q00030A3Q0052756E436F2Q6D616E64030C3Q00496E766F6B65536572766572030B3Q0053652Q6C436F6E6669726D03063Q004261736B6574000A4Q006D7Q00206Q000100206Q000200122Q000200036Q00033Q00014Q000400013Q00102Q0003000400046Q00039Q008Q00017Q00013Q0003073Q0044657374726F7900044Q000B7Q0020D95Q00012Q000E012Q000200012Q00E33Q00017Q00023Q0003053Q0056616C7565029Q00034Q000B7Q0030723Q000100022Q00E33Q00017Q00043Q00030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q0052752Q6E696E6700074Q00197Q00206Q000100122Q000200023Q00202Q00020002000300202Q0002000200046Q000200016Q00017Q00023Q0003083Q004D6F76656D656E7403243Q005265736574206461736820632Q6F6C646F776E2076696120506C6179657253746174757300104Q000B8Q00DD3Q0001000200067B3Q000F00013Q0004443Q000F000100200600013Q000100067B0001000F00013Q0004443Q000F00012Q000B000100013Q00200600023Q00012Q00D500010002000200067B0001000F00013Q0004443Q000F00012Q000B000100023Q001200010200024Q000E2Q01000200012Q00E33Q00017Q000F3Q00030E3Q0046696E6446697273744368696C6403063Q0053686172656403083Q005061636B6167657303043Q004B6E697403073Q0072657175697265030D3Q00476574436F6E74726F2Q6C657203103Q00506C61796572436F6E74726F2Q6C657203063Q0053746174757303043Q004461746103083Q004D6F76656D656E7403383Q00526573657420506C61796572436F6E74726F2Q6C65722E5374617475732E446174612E4D6F76656D656E742E44617368432Q6F6C646F776E03133Q00436861726163746572436F6E74726F2Q6C657203093Q00432Q6F6C646F776E7303123Q005374616D696E61496E746572666163654364029Q003A4Q00567Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q0004443Q000900010020D900013Q0001001200010300034Q00890001000300020006950002000E000100010004443Q000E00010020D9000200010001001200010400044Q008900020004000200067B0002003900013Q0004443Q0039000100120C010300054Q005B000400024Q00D500030002000200200600040003000600067B0004003900013Q0004443Q00390001002006000400030006001200010500074Q00D500040002000200067B0004002F00013Q0004443Q002F000100200600050004000800067B0005002F00013Q0004443Q002F000100200600050004000800200600060005000900067B0006002F00013Q0004443Q002F000100200600060005000900200600060006000A00067B0006002F00013Q0004443Q002F00012Q000B000600013Q00200600070005000900200600070007000A2Q00D500060002000200067B0006002F00013Q0004443Q002F00012Q000B000600023Q0012000107000B4Q000E0106000200010020060005000300060012000106000C4Q00D500050002000200067B0005003900013Q0004443Q0039000100200600060005000D00067B0006003900013Q0004443Q0039000100200600060005000D0030720006000E000F2Q00E33Q00017Q000A3Q0003073Q007265717569726503063Q00536861726564030B3Q00496E707574416374696F6E03063Q00556E6C6F636B03043Q00456E756D03073Q004B6579436F646503013Q0051031E3Q00556E6C6F636B65642051206B65792076696120496E707574416374696F6E03093Q00556E6C6F636B412Q6C03053Q00436C656172001D3Q0012C63Q00016Q00015Q00202Q00010001000200202Q0001000100036Q0002000200064Q001C00013Q0004443Q001C000100200600013Q000400067B0001001200013Q0004443Q001200010020D900013Q0004001238000300053Q00202Q00030003000600202Q0003000300074Q0001000300014Q000100013Q00122Q000200086Q00010002000100200600013Q000900067B0001001700013Q0004443Q001700010020D900013Q00092Q000E2Q010002000100200600013Q000A00067B0001001C00013Q0004443Q001C00010020D900013Q000A2Q000E2Q01000200012Q00E33Q00017Q000F3Q00030D3Q00506C6174666F726D5374616E6401002Q033Q0053697403093Q0057616C6B53702Q6564028Q0003093Q004A756D70506F77657203053Q007063612Q6C03083Q00416E63686F726564030E3Q0046696E6446697273744368696C6403063Q0053746174757303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q00422Q6F6C56616C756503043Q004E616D6500424Q000B7Q00067B3Q001900013Q0004443Q001900012Q000B7Q0030183Q000100029Q0000304Q000300029Q0000206Q000400264Q000E000100050004443Q000E00012Q000B8Q000B000100013Q00101C3Q000400012Q000B7Q0020065Q00060026683Q0015000100050004443Q001500012Q000B8Q000B000100023Q00101C3Q0006000100120C012Q00073Q00066700013Q000100012Q000B8Q000E012Q000200012Q000B3Q00033Q00067B3Q002200013Q0004443Q002200012Q000B3Q00033Q0020065Q000800067B3Q002200013Q0004443Q002200012Q000B3Q00033Q0030723Q000800022Q000B3Q00044Q00DD3Q000100020006950001002900013Q0004443Q002900010020D900013Q00090012000103000A4Q008900010003000200067B0001004100013Q0004443Q0041000100120C0102000B3Q0020D900030001000C2Q0043000300044Q007700023Q00040004443Q003F00010020D900070006000D0012000109000E4Q008900070009000200067B0007003E00013Q0004443Q003E00012Q000B000700053Q00200600080006000F2Q00D500070002000200067B0007003E00013Q0004443Q003E000100120C010700073Q00066700080001000100012Q005B3Q00064Q000E0107000200012Q00DC00055Q00068B00020030000100020004443Q003000012Q00E33Q00013Q00023Q00043Q00030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q0052752Q6E696E6700074Q00197Q00206Q000100122Q000200023Q00202Q00020002000300202Q0002000200046Q000200016Q00017Q00013Q0003073Q0044657374726F7900044Q000B7Q0020D95Q00012Q000E012Q000200012Q00E33Q00017Q00023Q0003043Q007461736B03053Q00737061776E00114Q000B7Q00067B3Q000400013Q0004443Q000400012Q00E33Q00013Q00120C012Q00013Q0020065Q000200066700013Q000100072Q000B3Q00014Q000B3Q00024Q000B3Q00034Q000B3Q00044Q000B3Q00054Q000B3Q00064Q000B8Q00D53Q000200022Q00ED8Q00E33Q00013Q00013Q000A3Q0003083Q004175746F53652Q6C03043Q007461736B03043Q0077616974026Q00E03F03043Q007469636B030C3Q0053652Q6C496E74657276616C03203Q004175746F2053652Q6C3A20547279696E67206E6F2D74656C65706F72743Q2E03063Q00787063612Q6C026Q00F03F033C3Q004175746F2053652Q6C3A204E6F2D74656C65706F7274206661696C65642C2066612Q6C6261636B20746F20666F7263652074656C65706F72743Q2E00414Q000B7Q0020065Q000100067B3Q003E00013Q0004443Q003E000100120C012Q00023Q00204F5Q000300122Q000100048Q000200019Q0000206Q000100064Q000D000100010004443Q000D00010004443Q003E00012Q000B3Q00013Q0006F85Q000100010004445Q000100120C012Q00054Q00D03Q000100024Q000100029Q0000014Q00015Q00202Q00010001000600062Q00013Q00013Q0004445Q00012Q000B3Q00033Q0012002Q0100074Q000E012Q0002000100120C012Q00083Q00066700013Q000100012Q000B3Q00043Q00066700020001000100032Q000B3Q00034Q000B3Q00014Q000B3Q00054Q00BA3Q000200010006950001002500013Q0004443Q002500010006F800013Q000100010004445Q00012Q000B00025Q00200600020002000100067B00023Q00013Q0004445Q000100120C010200023Q0020CF00020002000300122Q000300096Q0002000200014Q000200013Q00062Q00023Q000100010004445Q00012Q000B000200033Q0012000103000A4Q000E01020002000100120C010200083Q00066700030002000100012Q000B3Q00043Q00066700040003000100032Q000B3Q00034Q000B3Q00014Q000B3Q00054Q00B10002000400010004445Q00012Q0009017Q00ED3Q00064Q00E33Q00013Q00043Q00023Q00030A3Q006E6F54656C65706F72742Q0100064Q00D89Q0000013Q000100302Q0001000100026Q00019Q008Q00017Q00023Q0003103Q0053652Q6C4F6E636520652Q726F723A2003083Q00746F737472696E67010F4Q009100015Q00122Q000200013Q00122Q000300026Q00048Q0003000200024Q0002000200034Q0001000200014Q00018Q000100016Q000100026Q00028Q0001000200014Q00018Q000100028Q00017Q00023Q00030D3Q00666F72636554656C65706F72742Q0100054Q0016019Q00013Q000100302Q0001000100026Q000200016Q00017Q00023Q0003183Q0053652Q6C4F6E63652028666F7263652920652Q726F723A2003083Q00746F737472696E67010D4Q003400015Q00122Q000200013Q00122Q000300026Q00048Q0003000200024Q0002000200034Q0001000200014Q00018Q000100016Q000100026Q00028Q0001000200016Q00017Q00023Q0003083Q004175746F53652Q6C012Q00054Q00B77Q00304Q000100029Q006Q00018Q00017Q000C3Q0003083Q004175746F53652Q6C0100028Q0003053Q00706169727303023Q005F4703053Q00466F72676503103Q00506C617965725549456C656D656E7473030E3Q004175746F53652Q6C546F2Q676C6503053Q007063612Q6C03123Q0053652Q6C496E74657276616C536C6964657203133Q00536B69704661766F7269746573546F2Q676C6503183Q00436F6E66696720726573657420746F2064656661756C747300304Q00707Q00304Q000100029Q006Q00019Q008Q00023Q00124Q00038Q00033Q00124Q00046Q000100048Q0002000200044Q000E00012Q000B00056Q00BF00050003000400068B3Q000C000100020004443Q000C000100120C012Q00053Q0020065Q00060020065Q000700067B3Q002C00013Q0004443Q002C000100200600013Q000800067B0001001C00013Q0004443Q001C000100120C2Q0100093Q00066700023Q000100012Q005B8Q000E2Q010002000100200600013Q000A00067B0001002400013Q0004443Q0024000100120C2Q0100093Q00066700020001000100022Q005B8Q000B3Q00044Q000E2Q010002000100200600013Q000B00067B0001002C00013Q0004443Q002C000100120C2Q0100093Q00066700020002000100022Q005B8Q000B3Q00044Q000E2Q01000200012Q000B000100053Q0012000102000C4Q000E2Q01000200012Q00E33Q00013Q00033Q00023Q00030E3Q004175746F53652Q6C546F2Q676C652Q033Q0053657400064Q00A67Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003123Q0053652Q6C496E74657276616C536C696465722Q033Q00536574030C3Q0053652Q6C496E74657276616C00074Q00097Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003133Q00536B69704661766F7269746573546F2Q676C652Q033Q00536574030D3Q00536B69704661766F726974657300074Q00097Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00023Q00030A3Q006E6F54656C65706F72742Q0100064Q00D89Q0000013Q000100302Q0001000100026Q00019Q008Q00017Q00023Q00030D3Q00666F72636554656C65706F72742Q0100064Q00D89Q0000013Q000100302Q0001000100026Q00019Q008Q00017Q00043Q0003053Q00706169727303053Q007461626C6503063Q00696E7365727403043Q00736F7274001D4Q009A7Q00122Q000100016Q00028Q00010002000300044Q000A000100120C010500023Q0020060005000500032Q005B00066Q005B000700044Q00B100050007000100068B00010005000100010004443Q0005000100120C2Q0100014Q000B000200014Q00110001000200030004443Q0015000100120C010500023Q0020060005000500032Q005B00066Q005B000700044Q00B100050007000100068B00010010000100010004443Q0010000100120C2Q0100023Q0020F20001000100044Q00028Q0001000200016Q00028Q00017Q00043Q0003053Q00706169727303053Q007461626C6503063Q00696E7365727403043Q00736F727400124Q009A7Q00122Q000100016Q00028Q00010002000300044Q000A000100120C010500023Q0020060005000500032Q005B00066Q005B000700044Q00B100050007000100068B00010005000100010004443Q0005000100120C2Q0100023Q0020F20001000100044Q00028Q0001000200016Q00028Q00017Q00043Q0003053Q00706169727303053Q007461626C6503063Q00696E7365727403043Q00736F727400124Q009A7Q00122Q000100016Q00028Q00010002000300044Q000A000100120C010500023Q0020060005000500032Q005B00066Q005B000700044Q00B100050007000100068B00010005000100010004443Q0005000100120C2Q0100023Q0020F20001000100044Q00028Q0001000200016Q00028Q00017Q00023Q00030A3Q00446973636F2Q6E65637403103Q00436C65616E757020636F6D706C65746500104Q00599Q003Q000100016Q00018Q000100016Q00023Q00064Q000C00013Q0004443Q000C00012Q000B3Q00023Q0020D95Q00012Q000E012Q000200012Q0009017Q00ED3Q00024Q000B3Q00033Q0012002Q0100024Q000E012Q000200012Q00E33Q00017Q00723Q0003023Q006F7303053Q00636C6F636B03043Q007461736B03043Q0077616974026Q00E03F03023Q005F4703053Q00466F72676503043Q005461627303083Q004175746F53652Q6C03083Q005261796669656C64026Q00244003043Q007761726E03303Q005B4175746F53652Q6C2055495D20446570656E64656E63696573206E6F742072656164793B20554920736B692Q70656403123Q004175746F53652Q6C5549456C656D656E7473030F3Q0052657365744175746F53652Q6C5549030D3Q0043726561746553656374696F6E03103Q004155544F2053452Q4C20434F4E464947030E3Q004175746F53652Q6C546F2Q676C65030C3Q00437265617465546F2Q676C6503043Q004E616D65031B3Q004175746F2053652Q6C20284F726573202B20452Q73656E63657329030C3Q0043752Q72656E7456616C756503043Q00466C616703083Q0043612Q6C6261636B03123Q0053652Q6C496E74657276616C536C69646572030C3Q00437265617465536C6964657203133Q0053652Q6C20496E74657276616C20287365632903053Q0052616E6765025Q00C0724003093Q00496E6372656D656E74026Q001440030C3Q0053652Q6C496E74657276616C026Q003E4003103Q0047454E4552414C2053452Q54494E475303133Q00536B69704661766F7269746573546F2Q676C65030E3Q00536B6970204661766F7269746573030D3Q00536B69704661766F7269746573010003113Q0053652Q6C536B69704661766F7269746573030E3Q0053652Q6C4F726573546F2Q676C6503093Q0053652Q6C204F72657303083Q0053652Q6C4F726573030F3Q0053652Q6C4F726573456E61626C656403123Q0053652Q6C452Q73656E636573546F2Q676C65030D3Q0053652Q6C20452Q73656E636573030C3Q0053652Q6C452Q73656E63657303133Q0053652Q6C452Q73656E636573456E61626C6564030F3Q0053652Q6C52756E6573546F2Q676C65030A3Q0053652Q6C2052756E657303093Q0053652Q6C52756E657303103Q0053652Q6C52756E6573456E61626C6564030F3Q0044656275674D6F6465546F2Q676C65031D3Q004465627567204D6F646520284C6F672074726169742076616C7565732903093Q0044656275674D6F64652Q01030D3Q0053652Q6C44656275674D6F646503203Q004F52452046494C5445525320284B2Q45502073656C6563746564206F7265732903053Q007063612Q6C028Q0003053Q00706169727303053Q007461626C6503063Q00696E7365727403043Q00736F7274030F3Q00284E6F206F72657320666F756E6429030B3Q004372656174654C6162656C032E3Q00456D707479203D2073652Q6C20412Q4C207C2053656C6563746564203D204B2Q4550202870726F74656374656429030D3Q004F726546696C7465724C697374030E3Q0043726561746544726F70646F776E030C3Q004F72657320746F204B2Q455003073Q004F7074696F6E73030D3Q0043752Q72656E744F7074696F6E030F3Q004D756C7469706C654F7074696F6E7303283Q00452Q53454E43452046494C5445525320284B2Q45502073656C656374656420652Q73656E6365732903113Q00452Q73656E636546696C7465724C69737403103Q00452Q73656E63657320746F204B2Q455003273Q0052554E452F54524149542046494C54455253202853652Q6C204F4E4C592073656C656374656429032D3Q00456D707479203D2073652Q6C20412Q4C207C2053656C6563746564203D2073652Q6C204F4E4C592074686F7365032A3Q0056616C75652046696C746572732062656C6F772063616E2070726F7465637420672Q6F6420726F2Q6C73030E3Q0052756E6546696C7465724C69737403143Q0052756E65732F54726169747320746F2053652Q6C03203Q005155414C4954592046494C54455220284B2Q657020472Q6F6420526F2Q6C7329032D3Q0052756E6573207769746820414E5920737461742061626F7665207468697320252077692Q6C206265204B455054031E3Q0053657420746F203020746F2064697361626C65202873652Q6C20612Q6C29030B3Q005175616C697479496E666F030F3Q0043726561746550617261677261706803053Q005469746C65030F3Q0043752Q72656E742053652Q74696E6703073Q00436F6E74656E7403143Q0052756E655175616C6974795468726573686F6C64030D3Q005175616C697479536C6964657203163Q004B2Q6570205175616C697479205468726573686F6C64026Q00594003063Q0053752Q66697803013Q002503103Q005374726963744D6F6465546F2Q676C65032C3Q00537472696374204D6F64652028412Q4C20747261697473206D757374206D2Q6574207468726573686F6C642903113Q005374726963745175616C6974794D6F6465030C3Q0043726561746542752Q746F6E031C3Q00517569636B3A204B2Q657020476F6420526F2Q6C7320283930252B2903153Q00517569636B3A2053652Q6C20412Q6C2052756E6573030E3Q004D414E55414C20414354494F4E53030D3Q0053652Q6C4E6F7742752Q746F6E030D3Q00F09F92B02053652Q6C204E6F7703113Q0053652Q6C4E6F774E6F54656C65706F727403163Q0053652Q6C204E6F7720284E6F2054656C65706F72742903143Q0053652Q6C4E6F77466F72636554656C65706F7274031F3Q0053652Q6C204E6F772028466F7263652054656C65706F7274202F2046697829030E3Q0050414E4455414E2046494C54455203163Q00F09F938C2043617261204B65726A612046696C746572035A012Q004F5245202620452Q53454E43452046494C5445523A0AE280A2204B6F736F6E67203D204A75616C2053454D55410AE280A22050696C6968206974656D203D2053494D50414E2028746964616B2064696A75616C292Q0A52554E452F54524149542046494C5445523A0AE280A2204B6F736F6E67203D204A75616C2053454D55412072756E650AE280A22050696C6968207472616974203D204A75616C2048414E59412074726169742074657273656275742Q0A5155414C495459205448524553484F4C443A0AE280A2203025203D2044697361626C65640AE280A2203830252B203D2053696D70616E2072756E652064656E67616E20737461742062616775732Q0A535452494354204D4F44453A0AE280A2204F2Q46203D2053696D70616E206A696B6120312074726169742062616775730AE280A2204F4E203D2053696D70616E206A696B612053454D55412074726169742062616775730A03113Q00F09F939620436F6E746F6820536574757003DA3Q00E280A22053696D70616E204469616D6F6E64202620476F6C64206F72653A0A2Q204F72652046696C7465723A2050696C6968204469616D6F6E642C20476F6C642Q0AE280A2204A75616C2073656D75612072756E652C2073696D70616E20476F6420526F2Q6C3A0A2Q2052756E652046696C7465723A204B6F736F6E67207C205468726573686F6C643A203930252Q0AE280A2204A75616C20496365206A656C656B2C2073696D70616E204963652062616775733A0A2Q2052756E652046696C7465723A20496365207C205468726573686F6C643A203830250A03053Q007072696E7403163Q005B4175746F53652Q6C5D20554920437265617465642100D0012Q00120C012Q00013Q0020065Q00022Q00DD3Q0001000200120C2Q0100033Q00206900010001000400122Q000200056Q00010002000100122Q000100063Q00202Q00010001000700062Q0001001B00013Q0004443Q001B000100120C2Q0100063Q00200600010001000700200600010001000800067B0001001B00013Q0004443Q001B000100120C2Q0100063Q00200600010001000700200600010001000800200600010001000900067B0001001B00013Q0004443Q001B000100120C2Q0100063Q00200600010001000700200600010001000A0006F800010021000100010004443Q0021000100120C2Q0100013Q0020060001000100022Q00DD0001000100022Q0051000100013Q000ED2000B0003000100010004443Q0003000100120C2Q0100063Q00200600010001000700067B0001003500013Q0004443Q0035000100120C2Q0100063Q00200600010001000700200600010001000800067B0001003500013Q0004443Q0035000100120C2Q0100063Q00200600010001000700200600010001000800200600010001000900067B0001003500013Q0004443Q0035000100120C2Q0100063Q00200600010001000700200600010001000A0006F800010039000100010004443Q0039000100120C2Q01000C3Q0012000102000D4Q000E2Q01000200012Q00E33Q00013Q00120C2Q0100063Q0020F100010001000700202Q00010001000800202Q00010001000900122Q000200063Q00202Q00020002000700202Q00020002000A4Q00035Q00122Q000400063Q00202Q00040004000700102Q0004000E000300122Q000400063Q00202Q00040004000700028500055Q0010300004000F00054Q00045Q00202Q00050001001000122Q000700116Q00050007000100202Q0005000100134Q00073Q000400302Q0007001400154Q00085Q00202Q00080008000900062Q00080054000100010004443Q005400012Q00FD00085Q00101C00070016000800307200070017000900066700080001000100042Q005B3Q00044Q000B8Q000B3Q00014Q000B3Q00023Q002Q100107001800084Q00050007000200102Q00030012000500202Q00050001001A4Q00073Q000600302Q00070014001B4Q000800023Q00122Q0009000B3Q00122Q000A001D6Q00080002000100101C0007001C00080030720007001E001F2Q000B00085Q0020060008000800200006F80008006C000100010004443Q006C0001001200010800213Q00101C00070016000800307200070017002000066700080002000100012Q000B7Q0010030107001800084Q00050007000200102Q00030019000500202Q00050001001000122Q000700226Q00050007000100202Q0005000100134Q00073Q000400302Q0007001400244Q00085Q00202Q00080008002500262Q0008007E000100260004443Q007E00012Q006200086Q00FD000800013Q00101C00070016000800307200070017002700066700080003000100012Q000B7Q0010790007001800084Q00050007000200102Q00030023000500202Q0005000100134Q00073Q000400302Q0007001400294Q00085Q00202Q00080008002A00262Q0008008E000100260004443Q008E00012Q006200086Q00FD000800013Q00101C00070016000800307200070017002B00066700080004000100012Q000B7Q0010790007001800084Q00050007000200102Q00030028000500202Q0005000100134Q00073Q000400302Q00070014002D4Q00085Q00202Q00080008002E00262Q0008009E000100260004443Q009E00012Q006200086Q00FD000800013Q00101C00070016000800307200070017002F00066700080005000100012Q000B7Q0010790007001800084Q00050007000200102Q0003002C000500202Q0005000100134Q00073Q000400302Q0007001400314Q00085Q00202Q00080008003200262Q000800AE000100260004443Q00AE00012Q006200086Q00FD000800013Q00101C00070016000800307200070017003300066700080006000100012Q000B7Q0010540007001800084Q00050007000200102Q00030030000500202Q0005000100134Q00073Q000400302Q0007001400354Q00085Q00202Q00080008003600262Q000800BE000100370004443Q00BE00012Q006200086Q00FD000800013Q00101C00070016000800307200070017003800066700080007000100012Q000B7Q0010250007001800084Q00050007000200102Q00030034000500202Q00050001001000122Q000700396Q0005000700014Q00055Q00122Q0006003A6Q000700036Q00060002000700062Q000600D600013Q0004443Q00D6000100067B000700D600013Q0004443Q00D600012Q006F000800073Q000ED2003B00D6000100080004443Q00D600012Q005B000500073Q0004443Q00E5000100120C0108003C4Q000B000900044Q001100080002000A0004443Q00DF000100120C010C003D3Q002006000C000C003E2Q005B000D00054Q005B000E000B4Q00B1000C000E000100068B000800DA000100010004443Q00DA000100120C0108003D3Q00200600080008003F2Q005B000900054Q000E0108000200012Q006F000800053Q002668000800EC0001003B0004443Q00EC00012Q00E6000800013Q001200010900404Q00140108000100012Q005B000500083Q0020D90008000100410012F6000A00426Q0008000A000100202Q0008000100444Q000A3Q000600302Q000A0014004500102Q000A004600054Q000B5Q00202Q000B000B004300062Q000B00F8000100010004443Q00F800012Q00E6000B5Q00101C000A0047000B003072000A00480037003072000A00170043000667000B0008000100012Q000B7Q001017000A0018000B4Q0008000A000200102Q00030043000800202Q00080001001000122Q000A00496Q0008000A00014Q00085Q00122Q0009003C6Q000A00056Q00090002000B00044Q000D2Q0100120C010D003D3Q002006000D000D003E2Q005B000E00084Q005B000F000C4Q00B1000D000F000100068B000900082Q0100010004443Q00082Q0100120C0109003D3Q00202700090009003F4Q000A00086Q00090002000100202Q00090001004100122Q000B00426Q0009000B000100202Q0009000100444Q000B3Q000600302Q000B0014004B00102Q000B004600084Q000C5Q00202Q000C000C004A00062Q000C001F2Q0100010004443Q001F2Q012Q00E6000C5Q00101C000B0047000C003072000B00480037003072000B0017004A000667000C0009000100012Q000B7Q001017000B0018000C4Q0009000B000200102Q0003004A000900202Q00090001001000122Q000B004C6Q0009000B00014Q00095Q00122Q000A003C6Q000B00066Q000A0002000C00044Q00342Q0100120C010E003D3Q002006000E000E003E2Q005B000F00094Q005B0010000D4Q00B1000E0010000100068B000A002F2Q0100010004443Q002F2Q0100120C010A003D3Q00206B000A000A003F4Q000B00096Q000A0002000100202Q000A0001004100122Q000C004D6Q000A000C000100202Q000A0001004100122Q000C004E6Q000A000C000100202Q000A000100444Q000C3Q000600302Q000C0014005000102Q000C004600094Q000D5Q00202Q000D000D004F00062Q000D00492Q0100010004443Q00492Q012Q00E6000D5Q00101C000C0047000D003072000C00480037003072000C0017004F000667000D000A000100012Q000B7Q001055000C0018000D4Q000A000C000200102Q0003004F000A00202Q000A0001001000122Q000C00516Q000A000C000100202Q000A0001004100122Q000C00526Q000A000C000100202Q000A0001004100122Q000C00536Q000A000C0001000285000A000B3Q002050000B000100554Q000D3Q000200302Q000D005600574Q000E000A6Q000F5Q00202Q000F000F005900062Q000F00642Q0100010004443Q00642Q01001200010F003B4Q00D5000E00020002002Q10010D0058000E4Q000B000D000200102Q00030054000B00202Q000B0001001A4Q000D3Q000700302Q000D0014005B4Q000E00023Q00122Q000F003B3Q00122Q0010005C6Q000E0002000100101C000D001C000E0030B6000D001E001F00302Q000D005D005E4Q000E5Q00202Q000E000E005900062Q000E00772Q0100010004443Q00772Q01001200010E003B3Q0020E8000E000E005C00101C000D0016000E003072000D00170059000667000E000C000100032Q000B8Q005B3Q00034Q005B3Q000A3Q001054000D0018000E4Q000B000D000200102Q0003005A000B00202Q000B000100134Q000D3Q000400302Q000D001400604Q000E5Q00202Q000E000E006100262Q000E00892Q0100370004443Q00892Q012Q0062000E6Q00FD000E00013Q00101C000D0016000E003072000D00170061000667000E000D000100022Q000B8Q005B3Q00023Q001016000D0018000E4Q000B000D000200102Q0003005F000B00202Q000B000100624Q000D3Q000200302Q000D00140063000667000E000E000100032Q000B8Q005B3Q00034Q005B3Q00023Q0010B5000D0018000E4Q000B000D000100202Q000B000100624Q000D3Q000200302Q000D00140064000667000E000F000100032Q000B8Q005B3Q00034Q005B3Q00023Q00105C000D0018000E4Q000B000D000100202Q000B0001001000122Q000D00656Q000B000D000100202Q000B000100624Q000D3Q000200302Q000D00140067000667000E0010000100012Q005B3Q00023Q001016000D0018000E4Q000B000D000200102Q00030066000B00202Q000B000100624Q000D3Q000200302Q000D00140069000667000E0011000100012Q005B3Q00023Q001016000D0018000E4Q000B000D000200102Q00030068000B00202Q000B000100624Q000D3Q000200302Q000D0014006B000667000E0012000100012Q005B3Q00023Q001003000D0018000E4Q000B000D000200102Q0003006A000B00202Q000B0001001000122Q000D006C6Q000B000D000100202Q000B000100554Q000D3Q000200302Q000D0056006D00302Q000D0058006E4Q000B000D000100202Q000B000100554Q000D3Q000200302Q000D0056006F00302Q000D005800704Q000B000D000100122Q000B00713Q00122Q000C00726Q000B000200016Q00013Q00133Q00033Q0003023Q005F4703053Q00466F72676503123Q004175746F53652Q6C5549456C656D656E747300053Q0012243Q00013Q00206Q00024Q00015Q00104Q000300016Q00017Q00013Q0003083Q004175746F53652Q6C01144Q000B00015Q00067B0001000400013Q0004443Q000400012Q00E33Q00014Q000B000100013Q00101C000100013Q00067B3Q000E00013Q0004443Q000E00012Q000B000100023Q00067B0001000E00013Q0004443Q000E00012Q000B000100024Q000F0001000100010004443Q001300012Q000B000100033Q00067B0001001300013Q0004443Q001300012Q000B000100034Q000F0001000100012Q00E33Q00017Q00013Q00030C3Q0053652Q6C496E74657276616C01034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q00030D3Q00536B69704661766F726974657301034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q0003083Q0053652Q6C4F72657301034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q00030C3Q0053652Q6C452Q73656E63657301034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q0003093Q0053652Q6C52756E657301034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q0003093Q0044656275674D6F646501034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q00030D3Q004F726546696C7465724C69737401034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q0003113Q00452Q73656E636546696C7465724C69737401034Q000B00015Q00101C000100014Q00E33Q00017Q00013Q00030E3Q0052756E6546696C7465724C69737401034Q000B00015Q00101C000100014Q00E33Q00017Q000E3Q00028Q0003193Q0044697361626C6564202873652Q6C20612Q6C2072756E65732902CD5QCCEC3F03153Q004B2Q657020476F6420526F2Q6C7320283930252B29029A5Q99E93F03153Q004B2Q6570205665727920472Q6F6420283830252B29026Q66E63F03103Q004B2Q657020472Q6F6420283730252B29026Q00E03F03133Q004B2Q6570204D656469756D2B20283530252B2903063Q00737472696E6703063Q00666F726D6174030C3Q004B2Q657020252E30662Q252B026Q005940011B3Q0026683Q0004000100010004443Q000400010012002Q0100024Q00BD000100023Q000E940003000800013Q0004443Q000800010012002Q0100044Q00BD000100023Q000E940005000C00013Q0004443Q000C00010012002Q0100064Q00BD000100023Q000E940007001000013Q0004443Q001000010012002Q0100084Q00BD000100023Q000E940009001400013Q0004443Q001400010012002Q01000A4Q00BD000100023Q00120C2Q01000B3Q0020F900010001000C00122Q0002000D3Q00202Q00033Q000E4Q000100036Q00019Q0000017Q00073Q0003143Q0052756E655175616C6974795468726573686F6C64026Q005940030B3Q005175616C697479496E666F2Q033Q0053657403053Q005469746C65030F3Q0043752Q72656E742053652Q74696E6703073Q00436F6E74656E74010E4Q006500015Q00202Q00023Q000200102Q0001000100024Q000100013Q00202Q00010001000300202Q0001000100044Q00033Q000200302Q0003000500064Q000400023Q00202Q00053Q00024Q00040002000200102Q0003000700044Q0001000300016Q00017Q00093Q0003113Q005374726963745175616C6974794D6F646503273Q004F4E202D20412Q4C20747261697473206D7573742062652061626F7665207468726573686F6C6403263Q004F2Q46202D204F6E6C79204F4E45207472616974206E2Q65647320746F2062652061626F766503063Q004E6F7469667903053Q005469746C65030B3Q00537472696374204D6F646503073Q00436F6E74656E7403083Q004475726174696F6E027Q004001104Q000B00015Q00101C000100013Q00067B3Q000700013Q0004443Q000700010012002Q0100023Q0006F800010008000100010004443Q000800010012002Q0100034Q000B000200013Q0020EC0002000200044Q00043Q000300302Q00040005000600102Q00040007000100302Q0004000800094Q0002000400016Q00017Q000F3Q0003143Q0052756E655175616C6974795468726573686F6C6402CD5QCCEC3F030D3Q005175616C697479536C696465722Q033Q00536574025Q00805640030B3Q005175616C697479496E666F03053Q005469746C65030F3Q0043752Q72656E742053652Q74696E6703073Q00436F6E74656E7403153Q004B2Q657020476F6420526F2Q6C7320283930252B2903063Q004E6F74696679030E3Q005175616C6974792046696C74657203203Q0053657420746F20393025202D204F6E6C7920476F6420526F2Q6C73206B65707403083Q004475726174696F6E027Q004000164Q00207Q00304Q000100026Q00013Q00206Q000300206Q000400122Q000200058Q000200016Q00013Q00206Q000600206Q00044Q00023Q000200302Q00020007000800302Q00020009000A6Q000200016Q00023Q00206Q000B4Q00023Q000300302Q00020007000C00302Q00020009000D00302Q0002000E000F6Q000200016Q00017Q000E3Q0003143Q0052756E655175616C6974795468726573686F6C64028Q00030D3Q005175616C697479536C696465722Q033Q00536574030B3Q005175616C697479496E666F03053Q005469746C65030F3Q0043752Q72656E742053652Q74696E6703073Q00436F6E74656E7403193Q0044697361626C6564202873652Q6C20612Q6C2072756E65732903063Q004E6F74696679030E3Q005175616C6974792046696C74657203213Q0044697361626C6564202D20412Q6C2072756E65732077692Q6C20626520736F6C6403083Q004475726174696F6E027Q004000164Q00207Q00304Q000100026Q00013Q00206Q000300206Q000400122Q000200028Q000200016Q00013Q00206Q000500206Q00044Q00023Q000200302Q00020006000700302Q0002000800096Q000200016Q00023Q00206Q000A4Q00023Q000300302Q00020006000B00302Q00020008000C00302Q0002000D000E6Q000200016Q00017Q000C3Q0003023Q005F4703053Q00466F72676503083Q0053652Q6C4F6E636503043Q007461736B03053Q00737061776E03063Q004E6F7469667903053Q005469746C6503043Q0053652Q6C03073Q00436F6E74656E7403163Q0053652Q6C206D6F64756C65206E6F74206C6F6164656403083Q004475726174696F6E027Q004000143Q00120C012Q00013Q0020065Q00020020065Q000300067B3Q000C00013Q0004443Q000C000100120C012Q00043Q0020DF5Q000500122Q000100013Q00202Q00010001000200202Q0001000100036Q0002000100044Q001300012Q000B7Q0020C35Q00064Q00023Q000300302Q00020007000800302Q00020009000A00302Q0002000B000C6Q000200012Q00E33Q00017Q000C3Q0003023Q005F4703053Q00466F72676503123Q0053652Q6C4F6E63654E6F54656C65706F727403043Q007461736B03053Q00737061776E03063Q004E6F7469667903053Q005469746C6503043Q0053652Q6C03073Q00436F6E74656E7403163Q0053652Q6C206D6F64756C65206E6F74206C6F6164656403083Q004475726174696F6E027Q004000143Q00120C012Q00013Q0020065Q00020020065Q000300067B3Q000C00013Q0004443Q000C000100120C012Q00043Q0020DF5Q000500122Q000100013Q00202Q00010001000200202Q0001000100036Q0002000100044Q001300012Q000B7Q0020C35Q00064Q00023Q000300302Q00020007000800302Q00020009000A00302Q0002000B000C6Q000200012Q00E33Q00017Q000C3Q0003023Q005F4703053Q00466F72676503153Q0053652Q6C4F6E6365466F72636554656C65706F727403043Q007461736B03053Q00737061776E03063Q004E6F7469667903053Q005469746C6503043Q0053652Q6C03073Q00436F6E74656E7403163Q0053652Q6C206D6F64756C65206E6F74206C6F6164656403083Q004475726174696F6E027Q004000143Q00120C012Q00013Q0020065Q00020020065Q000300067B3Q000C00013Q0004443Q000C000100120C012Q00043Q0020DF5Q000500122Q000100013Q00202Q00010001000200202Q0001000100036Q0002000100044Q001300012Q000B7Q0020C35Q00064Q00023Q000300302Q00020007000800302Q00020009000A00302Q0002000B000C6Q000200012Q00E33Q00017Q00", GetFEnv(), ...);
