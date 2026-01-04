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
				if (Enum <= 67) then
					if (Enum <= 33) then
						if (Enum <= 16) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum == 0) then
											local K;
											local B;
											local A;
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
											if (Stk[Inst[2]] <= Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									elseif (Enum == 2) then
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = #Stk[Inst[3]];
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
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
										local Results;
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
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
								elseif (Enum == 6) then
									Stk[Inst[2]] = Inst[3] ~= 0;
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
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum == 8) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								elseif (Enum == 10) then
									Stk[Inst[2]] = {};
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
							elseif (Enum <= 13) then
								if (Enum == 12) then
									local B;
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
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
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									Stk[Inst[2]]();
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
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 14) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Enum > 15) then
								local Edx;
								local Results;
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
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 24) then
							if (Enum <= 20) then
								if (Enum <= 18) then
									if (Enum > 17) then
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								elseif (Enum == 19) then
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
									if (Inst[2] < Stk[Inst[4]]) then
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
								end
							elseif (Enum <= 22) then
								if (Enum > 21) then
									local Edx;
									local Results;
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
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
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
									VIP = Inst[3];
								end
							elseif (Enum == 23) then
								local Edx;
								local Results;
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
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								if (Enum == 25) then
									Stk[Inst[2]] = {};
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum == 27) then
								local K;
								local B;
								local A;
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
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 30) then
							if (Enum > 29) then
								local K;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A]());
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
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
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
						elseif (Enum <= 31) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum == 32) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
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
						end
					elseif (Enum <= 50) then
						if (Enum <= 41) then
							if (Enum <= 37) then
								if (Enum <= 35) then
									if (Enum == 34) then
										local A = Inst[2];
										Stk[A](Stk[A + 1]);
									elseif (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 36) then
									do
										return Stk[Inst[2]];
									end
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 39) then
								if (Enum == 38) then
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
								end
							elseif (Enum == 40) then
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
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum <= 45) then
							if (Enum <= 43) then
								if (Enum == 42) then
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
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum > 44) then
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
								Stk[Inst[2]] = Env[Inst[3]];
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
						elseif (Enum <= 47) then
							if (Enum == 46) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							else
								local Edx;
								local Results, Limit;
								local B;
								local A;
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
								VIP = Inst[3];
							end
						elseif (Enum <= 48) then
							local Edx;
							local Results;
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
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
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
						elseif (Enum == 49) then
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
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 58) then
						if (Enum <= 54) then
							if (Enum <= 52) then
								if (Enum > 51) then
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
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
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
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum == 53) then
								if (Stk[Inst[2]] ~= Inst[4]) then
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
							end
						elseif (Enum <= 56) then
							if (Enum == 55) then
								local A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
							else
								local A;
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
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum > 57) then
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
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local K;
							local B;
							local A;
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
						end
					elseif (Enum <= 62) then
						if (Enum <= 60) then
							if (Enum == 59) then
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum == 61) then
							local K;
							local B;
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
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 64) then
						if (Enum == 63) then
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
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 65) then
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					elseif (Enum > 66) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
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
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 101) then
					if (Enum <= 84) then
						if (Enum <= 75) then
							if (Enum <= 71) then
								if (Enum <= 69) then
									if (Enum == 68) then
										local B;
										local A;
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
									elseif Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 70) then
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
									VIP = Inst[3];
								elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 73) then
								if (Enum == 72) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
							elseif (Enum == 74) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local K;
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
								VIP = Inst[3];
							end
						elseif (Enum <= 79) then
							if (Enum <= 77) then
								if (Enum == 76) then
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum > 78) then
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
									if (Mvm[1] == 62) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 81) then
							if (Enum == 80) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								local Edx;
								local Results, Limit;
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
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
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
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
						elseif (Enum <= 82) then
							local Edx;
							local Results;
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 83) then
							local B;
							local A;
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
					elseif (Enum <= 92) then
						if (Enum <= 88) then
							if (Enum <= 86) then
								if (Enum > 85) then
									do
										return;
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
								end
							elseif (Enum > 87) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 90) then
							if (Enum > 89) then
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
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 91) then
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 96) then
						if (Enum <= 94) then
							if (Enum > 93) then
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
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum == 95) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local Edx;
							local Results, Limit;
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
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
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
					elseif (Enum <= 98) then
						if (Enum == 97) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
						end
					elseif (Enum <= 99) then
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
					elseif (Enum == 100) then
						do
							return Stk[Inst[2]]();
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
				elseif (Enum <= 118) then
					if (Enum <= 109) then
						if (Enum <= 105) then
							if (Enum <= 103) then
								if (Enum > 102) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 104) then
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
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
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum <= 107) then
							if (Enum == 106) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
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
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 108) then
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							local Results;
							local K;
							local B;
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A]());
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
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
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
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
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
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
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
					elseif (Enum <= 113) then
						if (Enum <= 111) then
							if (Enum > 110) then
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
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local B;
								local Edx;
								local Results;
								local A;
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
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 112) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A]());
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 115) then
						if (Enum == 114) then
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
							local B;
							local A;
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
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 116) then
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
					elseif (Enum > 117) then
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
						local A;
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
				elseif (Enum <= 127) then
					if (Enum <= 122) then
						if (Enum <= 120) then
							if (Enum == 119) then
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
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 121) then
							Stk[Inst[2]] = Inst[3];
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
					elseif (Enum <= 124) then
						if (Enum > 123) then
							local B;
							local Edx;
							local Results;
							local A;
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
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
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
							Stk[Inst[2]] = Env[Inst[3]];
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
					elseif (Enum <= 125) then
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
					elseif (Enum > 126) then
						local B;
						local A;
						Stk[Inst[2]] = Inst[3];
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
						do
							return Stk[A](Unpack(Stk, A + 1, Top));
						end
					end
				elseif (Enum <= 131) then
					if (Enum <= 129) then
						if (Enum == 128) then
							local Edx;
							local Results, Limit;
							local B;
							local A;
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
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
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
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum > 130) then
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
						local Edx;
						local Results;
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
				elseif (Enum <= 133) then
					if (Enum == 132) then
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
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 134) then
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
					Stk[Inst[2]] = {};
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Inst[4];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
				elseif (Enum == 135) then
					local A = Inst[2];
					local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
					local Edx = 0;
					for Idx = A, Inst[4] do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				else
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
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!5C3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C61796572030B3Q00482Q74705365727669636503393Q00682Q7470733A2Q2F7261772E67697468756275736572636F6E74656E742E636F6D2F6E6F6E63652D6E732F617365632Q7361642F6D61696E2F03083Q00546865466F72676503063Q00436F6E666967030F3Q002F436F6E6669674E616D652E74787403053Q007072696E7403193Q005B54686520466F7267655D204C6F6164696E672055493Q2E03023Q005F4703053Q00466F72676503073Q004261736555524C03053Q007063612Q6C030A3Q006C6F6164737472696E6703073Q00482Q7470476574031C3Q00682Q7470733A2Q2F7369726975732E6D656E752F7261796669656C64030C3Q0043726561746557696E646F7703043Q004E616D65030E3Q0054686520466F7267652076332E32030C3Q004C6F6164696E675469746C6503093Q0054686520466F726765030F3Q004C6F6164696E675375627469746C6503123Q004C6F6164696E67206D6F64756C65733Q2E03133Q00436F6E66696775726174696F6E536176696E6703073Q00456E61626C65642Q01030A3Q00466F6C6465724E616D6503083Q0046696C654E616D6503093Q004B657953797374656D010003093Q0043726561746554616203043Q004661726D022Q00A0E9AAB3F04103063Q004D696E696E6703083Q0054656C65706F72742Q033Q00466C792Q033Q0046505303063Q00506C6179657203083Q0053652Q74696E677303063Q0057696E646F7703083Q005261796669656C6403043Q005461627303053Q005574696C7303073Q00476574522Q6F74030C3Q00476574436C65616E4E616D6503073Q00436C65616E7570030B3Q00436F2Q6E656374696F6E73030D3Q0043726561746553656374696F6E030E3Q0053637269707420436F6E74726F6C030C3Q0043726561746542752Q746F6E030D3Q00556E6C6F61642053637269707403083Q0043612Q6C6261636B03153Q00466F72636520436C65616E7570205068797369637303043Q00496E666F030B3Q004372656174654C6162656C03123Q004175746F204661726D2026204D696E696E67030C3Q0044656275672026204C6F6773030C3Q00437265617465546F2Q676C65030F3Q0053686F77204C6F672057696E646F77030C3Q0043752Q72656E7456616C756503043Q00466C6167030D3Q0053686F774C6F6757696E646F77030E3Q005265736574202620436F6E66696703183Q00526573657420412Q6C202620436C65617220436F6E666967030B3Q00437265617465496E707574030B3Q00436F6E666967204E616D65030F3Q00506C616365686F6C64657254657874030B3Q00436F6E666967206E616D6503183Q0052656D6F7665546578744166746572466F6375734C6F7374030B3Q005361766520436F6E666967030B3Q004C6F616420436F6E66696703043Q006661726D03063Q006D696E696E6703083Q0074656C65706F72742Q033Q006574632Q033Q0066707303063Q00706C61796572030C3Q0063616D6572615F7368616B6503043Q0073652Q6C030A3Q006175746F5F666F726765030D3Q00726567696F6E5F627970612Q7303043Q007461736B03053Q00737061776E03063Q004E6F7469667903053Q005469746C6503073Q00436F6E74656E74031D3Q005549205265616479202D204C6F6164696E67206D6F64756C65733Q2E03083Q004475726174696F6E026Q000840031E3Q005B54686520466F7267655D204D61696E206C6F6164657220726561647921001B012Q0012333Q00013Q00206Q000200122Q000200038Q0002000200202Q00013Q000400122Q000200013Q00202Q00020002000200122Q000400056Q00020004000200122Q000300063Q001279000400073Q001279000500084Q003E000600043Q001279000700094Q004100060006000700022900075Q00064E00080001000100022Q003E3Q00074Q003E3Q00053Q00064E00090002000100032Q003E3Q00064Q003E3Q00084Q003E3Q00053Q00064E000A0003000100032Q003E3Q00044Q003E3Q00084Q003E3Q00064Q002C000B00096Q000B000100024Q000C000B3Q00122Q000D000A3Q00122Q000E000B6Q000D0002000100122Q000D000C3Q00202Q000D000D000D00062Q000D0028000100010004153Q0028000100122B000D000C4Q0019000E5Q00101F000D000D000E00122B000D000C3Q002008000D000D000D00101F000D000E0003000229000D00043Q00122B000E000F3Q00064E000F0005000100012Q003E3Q00034Q0080000E0002000100122Q000E000A3Q00122Q000F000B6Q000E0002000100122Q000E00103Q00122Q000F00013Q00202Q000F000F001100122Q001100126Q000F00116Q000E3Q00022Q0058000E00010002002086000F000E00134Q00113Q000500302Q00110014001500302Q00110016001700302Q0011001800194Q00123Q000300302Q0012001B001C00102Q0012001D000400102Q0012001E000B00102Q0011001A001200304A0011001F00202Q0044000F0011000200202Q0010000F002100122Q001200223Q00122Q001300236Q00100013000200202Q0011000F002100122Q001300243Q00122Q001400236Q00110014000200202Q0012000F0021001236001400253Q00122Q001500236Q00120015000200202Q0013000F002100122Q001500263Q00122Q001600236Q0013001600020020240014000F0021001236001600273Q00122Q001700236Q00140017000200202Q0015000F002100122Q001700283Q00122Q001800236Q0015001800020020240016000F0021001279001800293Q001279001900234Q0001001600190002000229001700063Q000229001800073Q00122B0019000C3Q00200800190019000D0006260019006B000100010004153Q006B000100122B0019000C4Q0019001A5Q00101F0019000D001A00122B0019000C3Q00202A00190019000D00102Q0019002A000F00122Q0019000C3Q00202Q00190019000D00102Q0019002B000E0012310019000C3Q00202Q00190019000D4Q001A3Q000700102Q001A0022001000102Q001A0024001100102Q001A0025001200102Q001A0026001300102Q001A0027001400102Q001A0028001500102Q001A0029001600101F0019002C001A00121C0019000C3Q00202Q00190019000D4Q001A3Q000200102Q001A002E001700102Q001A002F001800102Q0019002D001A00122Q0019000C3Q00202Q00190019000D00202Q00190019003000062Q0019008B000100010004153Q008B000100122B0019000C3Q00200800190019000D2Q0019001A5Q00101F00190030001A00122B0019000C3Q00200800190019000D00200800190019003100062600190094000100010004153Q0094000100122B0019000C3Q00200800190019000D2Q0019001A5Q00101F00190031001A00122B0019000C3Q00201100190019000D00102Q0019000E000300202Q00190016003200122Q001B00336Q0019001B000200202Q001A001600344Q001C3Q000200302Q001C0014003500064E001D0008000100022Q003E3Q000D4Q003E3Q000E3Q00103F001C0036001D4Q001A001C000100202Q001A001600344Q001C3Q000200302Q001C0014003700064E001D0009000100022Q003E3Q000D4Q003E3Q000E3Q001055001C0036001D4Q001A001C000100202Q001A0016003200122Q001C00386Q001A001C000200202Q001B0016003900122Q001D00156Q001B001D000100202Q001B0016003900122Q001D003A4Q0061001B001D0001002004001B0016003200122Q001D003B6Q001B001D000200202Q001C0016003C4Q001E3Q000400302Q001E0014003D00302Q001E003E002000302Q001E003F0040000229001F000A3Q001042001E0036001F4Q001C001E000100202Q001C0016003200122Q001E00416Q001C001E000200202Q001D001600344Q001F3Q000200302Q001F0014004200064E0020000B000100022Q003E3Q000D4Q003E3Q000E3Q00101F001F003600202Q0061001D001F0001000229001D000C3Q000229001E000D3Q00064E001F000E000100032Q003E3Q00084Q003E3Q000C4Q003E3Q00043Q00064E0020000F000100022Q003E3Q000E4Q003E3Q001D3Q00064E00210010000100042Q003E3Q00044Q003E3Q00204Q003E3Q001F4Q003E3Q00023Q00064E00220011000100032Q003E3Q00024Q003E3Q000E4Q003E3Q001E4Q000C00235Q00202Q0024001600434Q00263Q000500302Q00260014004400102Q0026003E000C00302Q00260045004600302Q00260047002000064E00270012000100052Q003E3Q00234Q003E3Q00084Q003E3Q000C4Q003E3Q000A4Q003E3Q000E3Q00100E0026003600274Q00240026000200202Q0025001600344Q00273Q000200302Q00270014004800064E00280013000100032Q003E3Q00214Q003E3Q000E4Q003E3Q001F3Q00103F0027003600284Q00250027000100202Q0025001600344Q00273Q000200302Q00270014004900064E00280014000100032Q003E3Q001F4Q003E3Q00224Q003E3Q000E3Q00105A0027003600284Q0025002700014Q0025000A3Q00122Q0026004A3Q00122Q0027004B3Q00122Q0028004C3Q00122Q0029004D3Q00122Q002A004E3Q00122Q002B004F3Q001288002C00503Q00122Q002D00513Q00122Q002E00523Q00122Q002F00536Q0025000A000100064E00260015000100012Q003E3Q00033Q00122B002700543Q00200800270027005500064E00280016000100032Q003E3Q00254Q003E3Q00264Q003E3Q000E4Q002200270002000100207D0027000E00564Q00293Q000300302Q00290057001500302Q00290058005900302Q0029005A005B4Q00270029000100122B0027000A3Q0012790028005C4Q00220027000200012Q00563Q00013Q00173Q00053Q0003083Q00746F737472696E67034Q0003043Q0067737562030C3Q005E25732A282E2D2925732A2403023Q002531010B3Q00122B000100013Q0006650002000400013Q0004153Q00040001001279000200024Q003200010002000200207A00010001000300122Q000300043Q00122Q000400056Q000100046Q00019Q0000017Q00043Q00034Q0003043Q006773756203093Q005B5E2577252D255F5D03013Q005F01114Q006700016Q003E00026Q003200010002000200266B00010007000100010004153Q000700012Q0067000200014Q0025000200023Q002024000200010002001279000400033Q001279000500044Q000100020005000200266B0002000F000100010004153Q000F00012Q0067000300014Q0025000300024Q0025000200024Q00563Q00017Q00033Q0003063Q00697366696C6503053Q007063612Q6C03083Q007265616466696C6500173Q00122B3Q00013Q0006453Q001400013Q0004153Q0014000100122B3Q00014Q006700016Q00323Q000200020006453Q001400013Q0004153Q0014000100122B3Q00023Q00122B000100034Q006700026Q00593Q000200010006453Q001400013Q0004153Q001400010006450001001400013Q0004153Q001400012Q0067000200014Q003E000300014Q000F000200034Q001A00026Q00673Q00024Q00253Q00024Q00563Q00017Q00043Q0003093Q00777269746566696C6503183Q0046696C6573797374656D206E6F742073752Q706F7274656403083Q006973666F6C646572030A3Q006D616B65666F6C646572011C3Q00122B000100013Q00062600010006000100010004153Q000600012Q000600015Q001279000200024Q0037000100033Q00122B000100033Q0006450001001100013Q0004153Q0011000100122B000100034Q006700026Q003200010002000200062600010011000100010004153Q0011000100122B000100044Q006700026Q00220001000200012Q0067000100014Q005700028Q00010002000200122Q000200016Q000300026Q000400016Q0002000400014Q000200016Q000300016Q000200038Q00017Q000B3Q0003063Q0069706169727303093Q00776F726B7370616365030B3Q004765744368696C6472656E03043Q004E616D65030B3Q004D61676963436172706574030F3Q004661726D4D6167696343617270657403093Q00466C79436172706574030E3Q0054656C65706F727443617270657403113Q004D696E696E674D6167696343617270657403083Q005A6F6E655061727403053Q007063612Q6C001B3Q00127B3Q00013Q00122Q000100023Q00202Q0001000100034Q000100029Q00000200044Q0018000100200800050004000400263500050013000100050004153Q0013000100263500050013000100060004153Q0013000100263500050013000100070004153Q0013000100263500050013000100080004153Q0013000100263500050013000100090004153Q0013000100266B000500170001000A0004153Q0017000100122B0006000B3Q00064E00073Q000100012Q003E3Q00044Q00220006000200012Q008300035Q0006773Q0006000100020004153Q000600012Q00563Q00013Q00013Q00013Q0003073Q0044657374726F7900044Q00677Q0020245Q00012Q00223Q000200012Q00563Q00017Q00043Q0003063Q00697366696C6503083Q006C6F67732E6C756103083Q006C6F616466696C6503053Q007063612Q6C00153Q00122B3Q00013Q0006453Q000D00013Q0004153Q000D000100122B3Q00013Q001279000100024Q00323Q000200020006453Q000D00013Q0004153Q000D000100122B3Q00033Q001279000100024Q00323Q000200022Q005B3Q000100010004153Q001400012Q00677Q0006453Q001400013Q0004153Q0014000100122B3Q00043Q00064E00013Q000100012Q00678Q00223Q000200012Q00563Q00013Q00013Q00063Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574030B3Q006C6F67732E6C75613F763D03083Q00746F737472696E6703043Q007469636B000F3Q00121E3Q00013Q00122Q000100023Q00202Q0001000100034Q00035Q00122Q000400043Q00122Q000500053Q00122Q000600066Q000600016Q00053Q00024Q0003000300054Q000400016Q000100049Q0000026Q000100016Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403053Q00546F72736F010C3Q00066C0001000A00013Q0004153Q000A000100202400013Q0001001279000300024Q00010001000300020006260001000A000100010004153Q000A000100202400013Q0001001279000300034Q00010001000300022Q0025000100024Q00563Q00017Q00053Q0003043Q006773756203043Q0025642B24034Q00030C3Q005E25732A282E2D2925732A2403023Q002531010A3Q00203A00013Q000100122Q000300023Q00122Q000400036Q00010004000200202Q00010001000100122Q000300043Q00122Q000400056Q0001000400024Q000100028Q00017Q00153Q0003053Q007072696E7403183Q005B54686520466F7267655D20556E6C6F6164696E673Q2E03023Q005F4703053Q00466F72676503093Q0052657365744661726D03053Q007063612Q6C030B3Q0052657365744D696E696E67030D3Q00526573657454656C65706F7274030E3Q0052657365744175746F466F726765030A3Q004661726D436F6E66696703083Q004175746F4661726D0100030C3Q004D696E696E67436F6E666967030A3Q004175746F4D696E696E6703073Q00436C65616E757003053Q007061697273030D3Q00556E6C6F6164436C65616E7570030B3Q00436F2Q6E656374696F6E73030A3Q00446973636F2Q6E6563740003203Q005B54686520466F7267655D20556E6C6F6164656420636F6D706C6574656C792100803Q0012383Q00013Q00122Q000100028Q0002000100124Q00033Q00206Q000400206Q000500064Q000D00013Q0004153Q000D000100122B3Q00063Q00122B000100033Q0020080001000100040020080001000100052Q00223Q0002000100122B3Q00033Q0020085Q00040020085Q00070006453Q001700013Q0004153Q0017000100122B3Q00063Q00122B000100033Q0020080001000100040020080001000100072Q00223Q0002000100122B3Q00033Q0020085Q00040020085Q00080006453Q002100013Q0004153Q0021000100122B3Q00063Q00122B000100033Q0020080001000100040020080001000100082Q00223Q0002000100122B3Q00033Q0020085Q00040020085Q00090006453Q002B00013Q0004153Q002B000100122B3Q00063Q00122B000100033Q0020080001000100040020080001000100092Q00223Q0002000100122B3Q00033Q0020085Q00040020085Q000A0006453Q003400013Q0004153Q0034000100122B3Q00033Q0020085Q00040020085Q000A00304A3Q000B000C00122B3Q00033Q0020085Q00040020085Q000D0006453Q003D00013Q0004153Q003D000100122B3Q00033Q0020085Q00040020085Q000D00304A3Q000E000C00122B3Q00033Q0020085Q00040020085Q000F0006453Q004D00013Q0004153Q004D000100122B3Q00103Q001217000100033Q00202Q00010001000400202Q00010001000F6Q0002000200044Q004B000100122B000500064Q003E000600044Q00220005000200010006773Q0048000100020004153Q004800012Q00678Q000D3Q0001000100124Q00033Q00206Q000400206Q001100064Q005F00013Q0004153Q005F000100122B3Q00103Q001217000100033Q00202Q00010001000400202Q0001000100116Q0002000200044Q005D000100122B000500064Q003E000600044Q00220005000200010006773Q005A000100020004153Q005A000100122B3Q00033Q0020085Q00040020085Q00120006453Q007600013Q0004153Q0076000100122B3Q00103Q001217000100033Q00202Q00010001000400202Q0001000100126Q0002000200044Q007400010006450004007300013Q0004153Q007300010020080005000400130006450005007300013Q0004153Q0073000100122B000500063Q00064E00063Q000100012Q003E3Q00044Q00220005000200012Q008300035Q0006773Q006A000100020004153Q006A000100122B3Q00033Q00304A3Q0004001400122B3Q00063Q00064E00010001000100012Q00673Q00014Q00853Q0002000100124Q00013Q00122Q000100158Q000200016Q00013Q00023Q00013Q00030A3Q00446973636F2Q6E65637400044Q00677Q0020245Q00012Q00223Q000200012Q00563Q00017Q00013Q0003073Q0044657374726F7900044Q00677Q0020245Q00012Q00223Q000200012Q00563Q00017Q00403Q0003053Q007072696E7403243Q005B54686520466F7267655D20466F72636520436C65616E757020737461727465643Q2E03023Q005F4703053Q00466F72676503093Q0052657365744661726D03053Q007063612Q6C030B3Q0052657365744D696E696E67030D3Q00526573657454656C65706F7274030B3Q00436F2Q6E656374696F6E7303053Q007061697273030A3Q00446973636F2Q6E65637403183Q005B436C65616E75705D20446973636F2Q6E65637465643A2003083Q00746F737472696E6703043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00436861726163746572030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030D3Q00506C6174666F726D5374616E640100030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503093Q0047652Q74696E67557003073Q0052696754797065030F3Q0048756D616E6F6964526967547970652Q033Q0052313503093Q00486970486569676874027Q0040028Q0003043Q004865616403053Q00546F72736F030A3Q00552Q706572546F72736F030A3Q004C6F776572546F72736F2Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103443Q005B436C65616E75705D20526573746F7265642043616E436F2Q6C69646520666F7220486561642F546F72736F206F6E6C79202864656661756C74206265686176696F722903103Q0048756D616E6F6964522Q6F745061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030E3Q0047657444657363656E64616E747303083Q00426F64794779726F030C3Q00426F647956656C6F63697479030C3Q00426F6479506F736974696F6E03093Q00426F6479466F726365030D3Q00416C69676E506F736974696F6E03103Q00416C69676E4F7269656E746174696F6E03073Q0044657374726F7903153Q005B436C65616E75705D2044657374726F7965643A2003093Q00436C612Q734E616D6503073Q00436C65616E757003063Q004E6F7469667903053Q005469746C6503103Q00436C65616E757020436F6D706C65746503073Q00436F6E74656E74031B3Q005068797369637320726573746F72656420746F206E6F726D616C2103083Q004475726174696F6E03233Q005B54686520466F7267655D20466F72636520436C65616E757020636F6D706C6574652100DE3Q0012273Q00013Q00122Q000100028Q0002000100124Q00033Q00206Q000400064Q002500013Q0004153Q0025000100122B3Q00033Q0020085Q00040020085Q00050006453Q001100013Q0004153Q0011000100122B3Q00063Q00122B000100033Q0020080001000100040020080001000100052Q00223Q0002000100122B3Q00033Q0020085Q00040020085Q00070006453Q001B00013Q0004153Q001B000100122B3Q00063Q00122B000100033Q0020080001000100040020080001000100072Q00223Q0002000100122B3Q00033Q0020085Q00040020085Q00080006453Q002500013Q0004153Q0025000100122B3Q00063Q00122B000100033Q0020080001000100040020080001000100082Q00223Q0002000100122B3Q00033Q0020085Q00040006453Q004B00013Q0004153Q004B000100122B3Q00033Q0020085Q00040020085Q00090006453Q004B00013Q0004153Q004B000100122B3Q000A3Q001217000100033Q00202Q00010001000400202Q0001000100096Q0002000200044Q004500010006450004004400013Q0004153Q0044000100200800050004000B0006450005004400013Q0004153Q0044000100122B000500063Q00064E00063Q000100012Q003E3Q00044Q001B00050002000100122Q000500013Q00122Q0006000C3Q00122Q0007000D6Q000800036Q0007000200024Q0006000600074Q0005000200012Q008300035Q0006773Q0034000100020004153Q0034000100122B3Q00033Q0020085Q00042Q001900015Q00101F3Q0009000100122B3Q000E3Q00204F5Q000F00122Q000200108Q0002000200202Q00013Q001100202Q00020001001200062Q000200BD00013Q0004153Q00BD0001002024000300020013001279000500144Q00010003000500020006450003006700013Q0004153Q0067000100304A00030015001600207300040003001700122Q000600183Q00202Q00060006001900202Q00060006001A4Q00040006000100202Q00040003001B00122Q000500183Q00202Q00050005001C00202Q00050005001D00062Q00040066000100050004153Q0066000100304A0003001E001F0004153Q0067000100304A0003001E00202Q0019000400043Q001288000500213Q00122Q000600223Q00122Q000700233Q00122Q000800246Q00040004000100122B0005000A4Q003E000600044Q00660005000200070004153Q007C0001002024000A000200132Q003E000C00094Q0001000A000C0002000645000A007C00013Q0004153Q007C0001002024000B000A0025001279000D00264Q0001000B000D0002000645000B007C00013Q0004153Q007C000100304A000A0027002800067700050071000100020004153Q0071000100122B000500013Q00127F000600296Q00050002000100202Q00050002001300122Q0007002A6Q00050007000200062Q00050089000100010004153Q00890001002024000500020013001279000700224Q00010005000700020006450005009100013Q0004153Q0091000100122B0006002C3Q00202A00060006002D00102Q0005002B000600122Q0006002C3Q00202Q00060006002D00102Q0005002E000600122B0006000A3Q00202400070002002F2Q0043000700084Q008700063Q00080004153Q00BB0001002024000B000A0025001279000D00304Q0001000B000D0002000626000B00B4000100010004153Q00B40001002024000B000A0025001279000D00314Q0001000B000D0002000626000B00B4000100010004153Q00B40001002024000B000A0025001279000D00324Q0001000B000D0002000626000B00B4000100010004153Q00B40001002024000B000A0025001279000D00334Q0001000B000D0002000626000B00B4000100010004153Q00B40001002024000B000A0025001279000D00344Q0001000B000D0002000626000B00B4000100010004153Q00B40001002024000B000A0025001279000D00354Q0001000B000D0002000645000B00BB00013Q0004153Q00BB0001002024000B000A00362Q0039000B0002000100122Q000B00013Q00122Q000C00373Q00202Q000D000A00384Q000C000C000D4Q000B0002000100067700060096000100020004153Q009600012Q006700036Q005B00030001000100122B000300033Q002008000300030004000645000300D300013Q0004153Q00D3000100122B000300033Q002008000300030004002008000300030039000645000300D300013Q0004153Q00D3000100122B0003000A3Q001217000400033Q00202Q00040004000400202Q0004000400394Q00030002000500044Q00D1000100122B000800064Q003E000900074Q0022000800020001000677000300CE000100020004153Q00CE00012Q0067000300013Q00207D00030003003A4Q00053Q000300302Q0005003B003C00302Q0005003D003E00302Q0005003F001F4Q00030005000100122B000300013Q001279000400404Q00220003000200012Q00563Q00013Q00013Q00013Q00030A3Q00446973636F2Q6E65637400044Q00677Q0020245Q00012Q00223Q000200012Q00563Q00017Q00043Q0003023Q005F4703053Q00466F72676503093Q0053686F774C6F67554903093Q00486964654C6F675549011A3Q00122B000100013Q0020080001000100020006450001001900013Q0004153Q001900010006453Q001000013Q0004153Q0010000100122B000100013Q0020080001000100020020080001000100030006450001001900013Q0004153Q0019000100122B000100013Q0020080001000100020020080001000100032Q005B0001000100010004153Q0019000100122B000100013Q0020080001000100020020080001000100040006450001001900013Q0004153Q0019000100122B000100013Q0020080001000100020020080001000100042Q005B0001000100012Q00563Q00017Q001C3Q0003023Q005F4703053Q00466F72676503073Q00436C65616E7570030D3Q00556E6C6F6164436C65616E7570030B3Q00436F2Q6E656374696F6E7303093Q0052657365744661726D030B3Q0052657365744D696E696E67030D3Q00526573657454656C65706F727403083Q00526573657446505303093Q00526573657453652Q6C030E3Q0052657365744175746F466F72676503083Q005265736574466C79030D3Q0052657365744D696E696E675549030D3Q005265736574506C617965725549030D3Q0043616D6572615368616B65554903043Q007479706503053Q00526573657403083Q0066756E6374696F6E03053Q007063612Q6C030B3Q0043616D6572615368616B6503053Q00706169727303063Q004E6F7469667903053Q005469746C65030E3Q00526573657420436F6D706C65746503073Q00436F6E74656E74031C3Q00412Q6C207265736574202620636F6E666967732064656C657465642103083Q004475726174696F6E026Q000840008F3Q00122B3Q00013Q0020085Q00020006263Q0007000100010004153Q0007000100122B3Q00014Q001900015Q00101F3Q0002000100122B3Q00013Q0020085Q00020020085Q00030006263Q0010000100010004153Q0010000100122B3Q00013Q0020085Q00022Q001900015Q00101F3Q0003000100122B3Q00013Q0020085Q00020020085Q00040006263Q0019000100010004153Q0019000100122B3Q00013Q0020085Q00022Q001900015Q00101F3Q0004000100122B3Q00013Q0020085Q00020020085Q00050006263Q0022000100010004153Q0022000100122B3Q00013Q0020085Q00022Q001900015Q00101F3Q000500010002298Q007500015Q00122Q000200013Q00202Q00020002000200202Q0002000200064Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q0002000200074Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q0002000200084Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q0002000200094Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000A4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000B4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000C4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000D4Q0001000200014Q00015Q00122Q000200013Q00202Q00020002000200202Q00020002000E4Q00010002000100122Q000100013Q00202Q00010001000200202Q00010001000F00062Q0001006400013Q0004153Q0064000100122B000100103Q001253000200013Q00202Q00020002000200202Q00020002000F00202Q0002000200114Q00010002000200262Q00010064000100120004153Q0064000100122B000100133Q00120B000200013Q00202Q00020002000200202Q00020002000F00202Q0002000200114Q00010002000100044Q0077000100122B000100013Q0020080001000100020020080001000100140006450001007700013Q0004153Q0077000100122B000100103Q001253000200013Q00202Q00020002000200202Q00020002001400202Q0002000200114Q00010002000200262Q00010077000100120004153Q0077000100122B000100133Q00126F000200013Q00202Q00020002000200202Q00020002001400202Q0002000200114Q00010002000100122B000100153Q001217000200013Q00202Q00020002000200202Q0002000200034Q00010002000300044Q0080000100122B000600134Q003E000700054Q00220006000200010006770001007D000100020004153Q007D00012Q006700016Q005B00010001000100122B000100133Q000229000200014Q00620001000200014Q000100013Q00202Q0001000100164Q00033Q000300302Q00030017001800302Q00030019001A00302Q0003001B001C4Q0001000300016Q00013Q00023Q00033Q0003043Q007479706503083Q0066756E6374696F6E03053Q007063612Q6C01093Q00122B000100014Q003E00026Q003200010002000200266B00010008000100020004153Q0008000100122B000100034Q003E00026Q00220001000200012Q00563Q00017Q00053Q0003083Q006973666F6C64657203083Q00546865466F72676503053Q00706169727303093Q006C69737466696C657303053Q007063612Q6C00163Q00122B3Q00013Q001279000100024Q00323Q000200020006453Q001500013Q0004153Q0015000100122B3Q00033Q001205000100043Q00122Q000200026Q000100029Q00000200044Q0010000100122B000500053Q00064E00063Q000100012Q003E3Q00044Q00220005000200012Q008300035Q0006773Q000B000100020004153Q000B000100122B3Q00053Q000229000100014Q00223Q000200012Q00563Q00013Q00023Q00013Q0003073Q0064656C66696C6500043Q00122B3Q00014Q006700016Q00223Q000200012Q00563Q00017Q00023Q0003093Q0064656C666F6C64657203083Q00546865466F72676500043Q00122B3Q00013Q001279000100024Q00223Q000200012Q00563Q00017Q00043Q0003013Q0052025Q00E06F4003013Q004703013Q0042010C4Q002D00013Q000300202Q00023Q000100202Q00020002000200102Q00010001000200202Q00023Q000300202Q00020002000200102Q00010003000200202Q00023Q000400202Q00020002000200102Q0001000400024Q000100028Q00017Q00053Q0003063Q00436F6C6F723303073Q0066726F6D52474203013Q005203013Q004703013Q004201083Q001269000100013Q00202Q00010001000200202Q00023Q000300202Q00033Q000400202Q00043Q00054Q000100046Q00019Q0000017Q00023Q0003013Q002F03053Q002E72666C64010C4Q006700015Q0006650002000400013Q0004153Q000400012Q0067000200014Q00320001000200022Q0040000200023Q00122Q000300016Q000400013Q00122Q000500026Q0002000200054Q000200028Q00017Q000D3Q0003053Q00706169727303053Q00466C61677303043Q007479706503053Q007461626C6503043Q0054797065030B3Q00436F6C6F725069636B657203053Q00436F6C6F7203063Q00747970656F66030C3Q0043752Q72656E7456616C756503073Q00622Q6F6C65616E0100030E3Q0043752Q72656E744B657962696E64030D3Q0043752Q72656E744F7074696F6E003E4Q000A7Q00122Q000100016Q00025Q00202Q00020002000200062Q00020007000100010004153Q000700012Q001900026Q00660001000200030004153Q003A000100122B000600034Q003E000700054Q003200060002000200266B0006003A000100040004153Q003A000100200800060005000500266B00060019000100060004153Q001900010020080006000500070006450006001900013Q0004153Q001900012Q0067000600013Q0020080007000500072Q00320006000200022Q00483Q000400060004153Q003A00012Q0020000600063Q00122B000700083Q0020080008000500092Q003200070002000200266B0007002F0001000A0004153Q002F000100200800070005000900266B000700240001000B0004153Q002400012Q000600065Q0004153Q003900010020080007000500090006650006002E000100070004153Q002E000100200800070005000C0006650006002E000100070004153Q002E000100200800070005000D0006650006002E000100070004153Q002E00010020080006000500070004153Q0039000100200800070005000900066500060039000100070004153Q0039000100200800070005000C00066500060039000100070004153Q0039000100200800070005000D00066500060039000100070004153Q003900010020080006000500072Q00483Q0004000600067700010009000100020004153Q000900012Q00253Q00024Q00563Q00017Q00053Q0003093Q00777269746566696C6503183Q0046696C6573797374656D206E6F742073752Q706F7274656403083Q006973666F6C646572030A3Q006D616B65666F6C646572030A3Q004A534F4E456E636F6465001E3Q00122B3Q00013Q0006263Q0006000100010004153Q000600012Q00067Q001279000100024Q00373Q00033Q00122B3Q00033Q0006453Q001100013Q0004153Q0011000100122B3Q00034Q006700016Q00323Q000200020006263Q0011000100010004153Q0011000100122B3Q00044Q006700016Q00223Q000200012Q00673Q00014Q00513Q0001000200122Q000100016Q000200026Q0002000100024Q000300033Q00202Q0003000300054Q00058Q000300056Q00013Q00014Q000100016Q000100028Q00017Q000B3Q0003063Q00697366696C6503173Q00436F6E6669672066696C65206E6F7420666F756E643A2003053Q007063612Q6C031C3Q004661696C656420746F206465636F646520636F6E666967206461746103053Q00706169727303053Q00466C6167730003043Q007479706503053Q007461626C652Q033Q0053657403083Q0066756E6374696F6E01393Q00122B000100013Q0006450001000800013Q0004153Q0008000100122B000100014Q003E00026Q00320001000200020006260001000D000100010004153Q000D00012Q000600015Q001279000200024Q003E00036Q00410002000200032Q0037000100033Q00122B000100033Q00064E00023Q000100022Q00678Q003E8Q006600010002000200062600010017000100010004153Q001700012Q000600035Q001279000400044Q0037000300033Q00122B000300054Q0067000400013Q0020080004000400060006260004001D000100010004153Q001D00012Q001900046Q00660003000200050004153Q003400012Q003C00080002000600263500080032000100070004153Q0032000100122B000900084Q003E000A00074Q003200090002000200266B00090032000100090004153Q0032000100122B000900083Q002008000A0007000A2Q003200090002000200266B000900320001000B0004153Q0032000100122B000900033Q00064E000A0001000100032Q003E3Q00074Q003E3Q00084Q00673Q00024Q00220009000200012Q008300086Q008300065Q0006770003001F000100020004153Q001F00012Q0006000300014Q0025000300024Q00563Q00013Q00023Q00023Q00030A3Q004A534F4E4465636F646503083Q007265616466696C6500084Q00607Q00206Q000100122Q000200026Q000300016Q000200039Q009Q008Q00017Q00053Q0003043Q0054797065030B3Q00436F6C6F725069636B657203043Q007479706503053Q007461626C652Q033Q0053657400154Q00677Q0020085Q000100266B3Q0010000100020004153Q0010000100122B3Q00034Q0067000100014Q00323Q0002000200266B3Q0010000100040004153Q001000012Q00677Q00202F5Q00054Q000200026Q000300016Q000200039Q00000100044Q001400012Q00677Q0020245Q00052Q0067000200014Q00613Q000200012Q00563Q00017Q000C3Q00030F3Q00436F6E6669674E616D65496E7075742Q033Q0053657403063Q004E6F7469667903053Q005469746C65030B3Q00436F6E666967204E616D6503073Q00436F6E74656E74030A3Q005361766564206173202703243Q00272E2052656C6F61642073637269707420746F20612Q706C79206175746F2D736176652E03083Q004475726174696F6E026Q00084003083Q00746F737472696E67026Q001040012E4Q006700015Q0006450001000600013Q0004153Q000600012Q000600016Q007000016Q00563Q00014Q0067000100014Q001800028Q0001000200024Q000100026Q000200036Q000300016Q00020002000300062Q0002002300013Q0004153Q002300010006020001001700013Q0004153Q001700012Q0006000400014Q006800045Q00122Q000400013Q00202Q0004000400024Q000600016Q0004000600012Q0067000400043Q00204B0004000400034Q00063Q000300302Q00060004000500122Q000700076Q000800013Q00122Q000900086Q00070007000900102Q00060006000700302Q00060009000A4Q00040006000100044Q002D00012Q0067000400043Q0020780004000400034Q00063Q000300302Q00060004000500122Q0007000B6Q000800036Q00070002000200102Q00060006000700302Q00060009000C4Q0004000600012Q00563Q00017Q000B3Q0003053Q007063612Q6C03063Q004E6F7469667903053Q005469746C6503053Q005361766564030B3Q0053617665204661696C656403073Q00436F6E74656E7403173Q00436F6E66696775726174696F6E20736176656420746F2003083Q00746F737472696E6703083Q004475726174696F6E027Q0040026Q00104000233Q00122B3Q00013Q00064E00013Q000100012Q00678Q007C3Q000200014Q000200013Q00202Q0002000200024Q00043Q000300064Q000C00013Q0004153Q000C0001001279000500043Q0006260005000D000100010004153Q000D0001001279000500053Q00101F0004000300050006453Q001600013Q0004153Q00160001001279000500074Q0067000600024Q00580006000100022Q004100050005000600062600050019000100010004153Q0019000100122B000500084Q003E000600014Q003200050002000200101F0004000600050006453Q001F00013Q0004153Q001F00010012790005000A3Q00062600050020000100010004153Q002000010012790005000B3Q00101F0004000900052Q00610002000400012Q00563Q00013Q00013Q00013Q0003053Q00652Q726F7200084Q00678Q00843Q000100010006263Q0007000100010004153Q0007000100122B000200014Q003E000300014Q00220002000200012Q00563Q00017Q000B3Q0003053Q007063612Q6C03063Q004E6F7469667903053Q005469746C6503063Q004C6F61646564030B3Q004C6F6164204661696C656403073Q00436F6E74656E74031A3Q00436F6E66696775726174696F6E206C6F616465642066726F6D2003083Q00746F737472696E6703083Q004475726174696F6E027Q0040026Q00104000243Q00122B3Q00013Q00064E00013Q000100022Q00678Q00673Q00014Q007C3Q000200014Q000200023Q00202Q0002000200024Q00043Q000300064Q000D00013Q0004153Q000D0001001279000500043Q0006260005000E000100010004153Q000E0001001279000500053Q00101F0004000300050006453Q001700013Q0004153Q00170001001279000500074Q006700066Q00580006000100022Q00410005000500060006260005001A000100010004153Q001A000100122B000500084Q003E000600014Q003200050002000200101F0004000600050006453Q002000013Q0004153Q002000010012790005000A3Q00062600050021000100010004153Q002100010012790005000B3Q00101F0004000900052Q00610002000400012Q00563Q00013Q00013Q00013Q0003053Q00652Q726F72000B4Q00309Q003Q000100024Q000100016Q00028Q00010002000200062Q0001000A000100010004153Q000A000100122B000300014Q003E000400024Q00220003000200012Q00563Q00017Q00133Q00027Q0040028Q0003063Q00697366696C6503083Q007265616466696C6503043Q002E6C756103053Q007063612Q6C03053Q007072696E7403213Q005B54686520466F7267655D204C6F61646564206C6F63616C206D6F64756C653A2003043Q007761726E03213Q005B54686520466F7267655D204661696C656420746F206C6F6164206C6F63616C2003023Q003A2003083Q00746F737472696E67026Q00F03F03143Q005B54686520466F7267655D204C6F616465643A20031B3Q005B54686520466F7267655D204661696C656420746F206C6F61642003093Q0020612Q74656D70742003043Q007461736B03043Q0077616974026Q00E03F014E3Q001279000100013Q001279000200023Q00122B000300033Q0006450003002600013Q0004153Q0026000100122B000300043Q0006450003002600013Q0004153Q0026000100122B000300034Q007200045Q00122Q000500056Q0004000400054Q00030002000200062Q0003002600013Q0004153Q0026000100122B000300063Q00064E00043Q000100012Q003E8Q00660003000200040006450003001D00013Q0004153Q001D000100122B000500073Q00125E000600086Q00078Q0006000600074Q0005000200014Q000500016Q000500023Q00044Q0026000100122B000500093Q00126A0006000A6Q00075Q00122Q0008000B3Q00122Q0009000C6Q000A00046Q0009000200024Q0006000600094Q00050002000100064C0002004B000100010004153Q004B000100201200020002000D00122B000300063Q00064E00040001000100032Q00678Q003E8Q003E3Q00024Q00660003000200040006450003003900013Q0004153Q0039000100122B000500073Q00125E0006000E6Q00078Q0006000600074Q0005000200014Q000500016Q000500023Q00044Q0026000100122B000500093Q00122Q0006000F6Q00075Q00122Q000800106Q000900023Q00122Q000A000B3Q00122Q000B000C6Q000C00046Q000B000200024Q00060006000B4Q00050002000100062Q00020026000100010004153Q0026000100122B000500113Q00200800050005001200105C0006001300022Q00220005000200010004153Q002600012Q000600036Q0025000300024Q00563Q00013Q00023Q00073Q0003083Q007265616466696C6503043Q002E6C7561030A3Q006C6F6164737472696E6703053Q00652Q726F7203163Q0053796E74617820452Q726F7220696E206C6F63616C2003023Q003A2003083Q00746F737472696E6700173Q0012523Q00016Q00015Q00122Q000200026Q0001000100026Q0002000200122Q000100036Q00028Q00010002000200062Q00010013000100010004153Q0013000100122B000300043Q001221000400056Q00055Q00122Q000600063Q00122Q000700076Q000800026Q0007000200024Q0004000400074Q0003000200012Q003E000300014Q0064000300014Q001A00036Q00563Q00017Q000D3Q0003073Q002E6C75613F763D03083Q00746F737472696E6703043Q007469636B03053Q007072696E7403163Q005B54686520466F7267655D204665746368696E673A20030A3Q002028612Q74656D70742003013Q002903043Q0067616D6503073Q00482Q7470476574030A3Q006C6F6164737472696E6703053Q00652Q726F7203103Q0053796E74617820452Q726F7220696E2003023Q003A2000274Q006D9Q00000100013Q00122Q000200013Q00122Q000300023Q00122Q000400036Q000400016Q00033Q00028Q000300122Q000100043Q00122Q000200056Q00035Q00122Q000400066Q000500023Q00122Q000600076Q0002000200064Q00010002000100122Q000100083Q00202Q0001000100094Q00038Q000400016Q00010004000200122Q0002000A6Q000300016Q00020002000300062Q00020023000100010004153Q0023000100122B0004000B3Q0012210005000C6Q000600013Q00122Q0007000D3Q00122Q000800026Q000900036Q0008000200024Q0005000500084Q0004000200012Q003E000400024Q0064000400014Q001A00046Q00563Q00017Q001F3Q0003043Q007461736B03043Q0077616974026Q00E03F028Q0003063Q00697061697273026Q33D33F026Q00F03F03053Q007461626C6503063Q00696E7365727403053Q007072696E7403133Q005B54686520466F7267655D204C6F616465642003013Q002F03083Q00206D6F64756C657303053Q007063612Q6C033A3Q005B54686520466F7267655D20536B692Q70696E67204C6F6164436F6E66696775726174696F6E20286E6F206D6F64756C6573206C6F616465642903063Q004E6F7469667903053Q005469746C6503093Q0054686520466F72676503073Q00436F6E74656E7403073Q004C6F6164656420030A3Q0020286661696C65643A2003063Q00636F6E63617403023Q002C2003013Q0029034Q0003013Q002103083Q004475726174696F6E026Q00084003073Q005761726E696E6703243Q004E6F206D6F64756C6573206C6F616465642E20436865636B207365727665722055524C2E026Q00144000583Q0012163Q00013Q00206Q000200122Q000100038Q0002000100124Q00046Q00015Q00122Q000200056Q00038Q00020002000400044Q001A000100122B000700013Q00207400070007000200122Q000800066Q0007000200014Q000700016Q000800066Q00070002000200062Q0007001500013Q0004153Q001500010020125Q00070004153Q001A000100122B000700083Q0020080007000700092Q003E000800014Q003E000900064Q00610007000900010006770002000A000100020004153Q000A000100122B0002000A3Q0012340003000B6Q00045Q00122Q0005000C6Q00068Q000600063Q00122Q0007000D6Q0003000300074Q00020002000100122Q000200013Q00202Q00020002000200122Q000300036Q000200020001000E2Q0004003000013Q0004153Q0030000100122B0002000E3Q00064E00033Q000100012Q00673Q00024Q00220002000200010004153Q0033000100122B0002000A3Q0012790003000F4Q0022000200020001000E230004005000013Q0004153Q005000012Q0067000200023Q0020130002000200104Q00043Q000300302Q00040011001200122Q000500146Q00065Q00122Q0007000D6Q000800013Q000E2Q00040049000100080004153Q00490001001279000800153Q00123D000900083Q00202Q0009000900164Q000A00013Q00122Q000B00176Q0009000B000200122Q000A00186Q00080008000A00062Q0008004A000100010004153Q004A0001001279000800193Q0012790009001A4Q004600050005000900102Q00040013000500302Q0004001B001C4Q00020004000100044Q005700012Q0067000200023Q00207D0002000200104Q00043Q000300302Q00040011001D00302Q00040013001E00302Q0004001B001F4Q0002000400012Q00563Q00013Q00013Q00013Q0003113Q004C6F6164436F6E66696775726174696F6E00044Q00677Q0020245Q00012Q00223Q000200012Q00563Q00017Q00", GetFEnv(), ...);
